import java.nio.file.Paths;
import java.util.ArrayList;
import scala.collection.immutable.List$;
import scala.jdk.javaapi.CollectionConverters;
import viper.silicon.SiliconFrontend;
import viper.silver.reporter.StdIOReporter;
import viper.silver.verifier.AbstractError;
import viper.silver.verifier.Failure;

public final class SourceSession {
    static class CaptureReporter extends StdIOReporter {
        final ArrayList<String> warnings = new ArrayList<>();
        CaptureReporter() { super("compatibility", false); }
        void add(scala.collection.Iterator<? extends AbstractError> it) {
            while (it.hasNext()) warnings.add(it.next().readableMessage());
        }
        @Override public void doReport(viper.silver.reporter.Message m) {
            if (m instanceof viper.silver.reporter.WarningsDuringParsing) add(((viper.silver.reporter.WarningsDuringParsing)m).warnings().iterator());
            if (m instanceof viper.silver.reporter.WarningsDuringTypechecking) add(((viper.silver.reporter.WarningsDuringTypechecking)m).warnings().iterator());
            if (m instanceof viper.silver.reporter.WarningsDuringVerification) add(((viper.silver.reporter.WarningsDuringVerification)m).warnings().iterator());
            super.doReport(m);
        }
    }
    static String q(String s) {
        StringBuilder b = new StringBuilder("\"");
        for (char c : s.toCharArray()) {
            if (c == '"' || c == '\\') b.append('\\').append(c);
            else if (c < 32) b.append(String.format("\\u%04x", (int)c));
            else b.append(c);
        }
        return b.append('"').toString();
    }
    static ArrayList<String> workerOptions(java.util.List<String> caller) {
        ArrayList<String> result = new ArrayList<>();
        if (caller.stream().noneMatch(s -> s.equals("--numberOfParallelVerifiers") || s.startsWith("--numberOfParallelVerifiers="))) {
            result.add("--numberOfParallelVerifiers"); result.add("1");
        }
        result.addAll(caller);
        return result;
    }
    public static void main(String[] args) {
        if (args.length < 2) throw new IllegalArgumentException("z3 path, then input files required");
        CaptureReporter reporter = new CaptureReporter();
        SiliconFrontend f = new SiliconFrontend(reporter, SiliconFrontend.$lessinit$greater$default$2());
        ArrayList<String> opts = new ArrayList<>();
        opts.add("--z3Exe"); opts.add(args[0]); opts.add("--disableCaches");
        int separator = 1;
        ArrayList<String> caller = new ArrayList<>();
        while (separator < args.length && !args[separator].equals("--")) caller.add(args[separator++]);
        opts.addAll(workerOptions(caller));
        if (separator + 1 >= args.length) throw new IllegalArgumentException("flags must be followed by -- and input files");
        int firstInput = separator + 1;
        opts.add(args[firstInput]);
        f._ver_$eq(f.createVerifier(String.join(" ", opts)));
        try {
            if (!f.prepare(List$.MODULE$.from(CollectionConverters.asScala(opts)))) throw new IllegalStateException("frontend prepare failed");
            f.init(f._ver());
            for (int i = firstInput; i < args.length; i++) {
                String path = args[i];
                reporter.warnings.clear();
                try {
                    f.reset(Paths.get(path));
                    f.runAllPhases();
                    var result = f.result();
                    if (f.errors().isEmpty()) { f.finish(); result = f.result(); }
                    StringBuilder line = new StringBuilder("{\"case\":").append(q(path));
                    line.append(",\"phase\":").append(q(f.state().toString()));
                    if (!(result instanceof Failure) && !result.getClass().getName().equals("viper.silver.verifier.Success$")) {
                        System.out.println("@@COMPAT@@{\"case\":" + q(path) + ",\"outcome\":\"unknown_result\",\"message\":" + q(result.getClass().getName()) + "}");
                        break;
                    }
                    line.append(",\"outcome\":").append(q(result instanceof Failure ? (((Failure)result).errors().isEmpty() ? "unknown_failure" : "failure") : "verified"));
                    line.append(",\"errors\":[");
                    if (result instanceof Failure) {
                        var it = ((Failure)result).errors().iterator(); boolean first = true;
                        while (it.hasNext()) {
                            AbstractError e = it.next();
                            if (!first) line.append(','); first = false;
                            line.append("{\"id\":").append(q(e.fullId())).append(",\"position\":").append(q(e.pos().toString())).append(",\"message\":").append(q(e.readableMessage())).append('}');
                        }
                    }
                    line.append("],\"warnings\":[");
                    for (int w = 0; w < reporter.warnings.size(); w++) { if (w > 0) line.append(','); line.append(q(reporter.warnings.get(w))); }
                    System.out.println("@@COMPAT@@" + line.append("]}"));
                } catch (Throwable e) {
                    System.out.println("@@COMPAT@@{\"case\":" + q(path) + ",\"outcome\":\"exception\",\"message\":" + q(e.toString()) + "}");
                    break; // Recovery after exceptional frontend state is not assumed.
                }
            }
        } finally {
            try { f._ver().stop(); }
            catch (Throwable e) {
                System.out.println("@@COMPAT@@{\"outcome\":\"cleanup_error\",\"message\":" + q(e.toString()) + "}");
            }
        }
    }
}
