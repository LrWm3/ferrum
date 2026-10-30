/** Reporter-only check; does not start a verifier or solver. */
public final class WarningCaptureTest {
    public static void main(String[] args) {
        for (String id : java.util.List.of("prover.interaction.failed", "external.tool.error", "exceptional.error", "dependencynotfound.error"))
            if (!SourceSession.isInfrastructureError(id)) throw new AssertionError(id);
        for (String id : java.util.List.of("timeout.error", "assert.failed:assertion.false"))
            if (SourceSession.isInfrastructureError(id)) throw new AssertionError(id);
        var reporter = new SourceSession.CaptureReporter();
        reporter.doReport(new viper.silver.reporter.AnnotationWarning("annotation warning test"));
        reporter.doReport(new viper.silver.reporter.InternalWarningMessage("internal warning test"));
        reporter.doReport(new viper.silver.reporter.ConfigurationWarning("configuration warning test"));
        var pos = viper.silver.ast.NoPosition$.MODULE$;
        var parse = new viper.silver.verifier.ParseWarning("parse test", pos);
        var type = new viper.silver.verifier.TypecheckerWarning("type test", pos);
        var verify = new viper.silver.verifier.VerifierWarning("verify test", pos);
        reporter.doReport(new viper.silver.reporter.WarningsDuringParsing(scala.collection.immutable.List$.MODULE$.from(scala.jdk.javaapi.CollectionConverters.asScala(java.util.List.of(parse)))));
        reporter.doReport(new viper.silver.reporter.WarningsDuringTypechecking(scala.collection.immutable.List$.MODULE$.from(scala.jdk.javaapi.CollectionConverters.asScala(java.util.List.of(type)))));
        reporter.doReport(new viper.silver.reporter.WarningsDuringVerification(scala.collection.immutable.List$.MODULE$.from(scala.jdk.javaapi.CollectionConverters.asScala(java.util.List.of(verify)))));
        if (!reporter.configurationWarningSnapshot().equals(java.util.List.of("configuration warning test"))) throw new AssertionError(reporter.configurationWarnings.toString());
        if (!reporter.warningSnapshot().equals(java.util.List.of("annotation warning test", "internal warning test", parse.readableMessage(), type.readableMessage(), verify.readableMessage()))) {
            throw new AssertionError(reporter.warnings.toString());
        }
        reporter.clearWarnings();
        if (!reporter.warningSnapshot().isEmpty() || reporter.configurationWarningSnapshot().size() != 1) throw new AssertionError("reset");
        var threads = new java.util.ArrayList<Thread>();
        for (int t = 0; t < 4; t++) {
            var thread = new Thread(() -> {
                for (int i = 0; i < 1000; i++) reporter.doReport(new viper.silver.reporter.InternalWarningMessage("concurrent"));
            });
            threads.add(thread); thread.start();
        }
        for (var thread : threads) try { thread.join(); } catch (InterruptedException e) { throw new AssertionError(e); }
        if (reporter.warningSnapshot().size() != 4000) throw new AssertionError("lost concurrent warnings");
        System.out.println("all six warning families captured");
    }
}
