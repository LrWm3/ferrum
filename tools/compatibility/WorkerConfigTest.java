import java.util.ArrayList;
import java.util.Arrays;
import scala.collection.immutable.List$;
import scala.jdk.javaapi.CollectionConverters;
import viper.silicon.Config;

/** Config-only parity check; does not start a verifier or solver. */
public final class WorkerConfigTest {
    static Config config(String input, String... caller) {
        ArrayList<String> options = SourceSession.workerOptions(Arrays.asList(caller));
        options.add(input);
        return new Config(List$.MODULE$.from(CollectionConverters.asScala(options)));
    }
    public static void main(String[] args) {
        String input = args[0];
        for (String[] options : new String[][] { {}, {"--numberOfParallelVerifiers", "2"}, {"--numberOfParallelVerifiers=2"} }) {
            Config config = config(input, options);
            if (config.error().isDefined()) throw new AssertionError(config.error().toString());
            int expected = options.length == 0 ? 1 : 2;
            if (!config.numberOfParallelVerifiers().apply().equals(expected)) throw new AssertionError("wrong worker count");
        }
        String[] duplicate = {"--numberOfParallelVerifiers", "1", "--numberOfParallelVerifiers=2"};
        if (!SourceSession.workerOptions(Arrays.asList(duplicate)).equals(Arrays.asList(duplicate))) throw new AssertionError("caller arguments changed");
        if (config(input, duplicate).error().isEmpty()) throw new AssertionError("source must reject duplicate worker options");
        System.out.println("worker option checks passed");
    }
}
