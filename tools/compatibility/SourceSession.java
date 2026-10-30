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
        final ArrayList<String> configurationWarnings = new ArrayList<>();
        CaptureReporter() { super("compatibility", false); }
        void add(scala.collection.Iterator<? extends AbstractError> it) {
            while (it.hasNext()) warnings.add(it.next().readableMessage());
        }
        synchronized void clearWarnings() { warnings.clear(); }
        synchronized ArrayList<String> warningSnapshot() { return new ArrayList<>(warnings); }
        synchronized ArrayList<String> configurationWarningSnapshot() { return new ArrayList<>(configurationWarnings); }
        @Override public synchronized void doReport(viper.silver.reporter.Message m) {
            if (m instanceof viper.silver.reporter.ConfigurationWarning) configurationWarnings.add(((viper.silver.reporter.ConfigurationWarning)m).text());
            if (m instanceof viper.silver.reporter.InternalWarningMessage) warnings.add(((viper.silver.reporter.InternalWarningMessage)m).text());
            if (m instanceof viper.silver.reporter.AnnotationWarning) warnings.add(((viper.silver.reporter.AnnotationWarning)m).text());
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
    static boolean isInfrastructureError(String id) {
        return id.equals("prover.interaction.failed") || id.equals("external.tool.error")
            || id.equals("exceptional.error") || id.equals("dependencynotfound.error");
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
                reporter.clearWarnings();
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
                    boolean proverError = false;
                    if (result instanceof Failure) {
                        var it = ((Failure)result).errors().iterator();
                        while (it.hasNext()) if (isInfrastructureError(it.next().fullId())) proverError = true;
                    }
                    line.append(",\"outcome\":").append(q(proverError ? "prover_error" : result instanceof Failure ? (((Failure)result).errors().isEmpty() ? "unknown_failure" : "failure") : "verified"));
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
                    var warnings = reporter.warningSnapshot();
                    for (int w = 0; w < warnings.size(); w++) { if (w > 0) line.append(','); line.append(q(warnings.get(w))); }
                    line.append("],\"configuration_warnings\":[");
                    var configurationWarnings = reporter.configurationWarningSnapshot();
                    for (int w = 0; w < configurationWarnings.size(); w++) { if (w > 0) line.append(','); line.append(q(configurationWarnings.get(w))); }
                    System.out.println("@@COMPAT@@" + line.append("]}"));
                    if (proverError) break; // A failed prover interaction can poison later sessions.
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
