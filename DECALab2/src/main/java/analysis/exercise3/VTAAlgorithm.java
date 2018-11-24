package analysis.exercise3;

import analysis.CallGraph;
import analysis.CallGraphAlgorithm;
import analysis.exercise1.CHAAlgorithm;
import org.graphstream.algorithm.TarjanStronglyConnectedComponents;
import org.graphstream.graph.Edge;
import org.graphstream.graph.Graph;
import org.graphstream.graph.Node;
import org.graphstream.graph.implementations.MultiGraph;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.Scene;
import soot.SootClass;
import soot.Value;
import soot.jimple.FieldRef;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

public class VTAAlgorithm extends CallGraphAlgorithm {

    private final Logger log = LoggerFactory.getLogger("VTA");

    @Override
    protected String getAlgorithm() {
        return "VTA";
    }

    @Override
    protected void populateCallGraph(Scene scene, CallGraph cg) {
        CallGraph initialCallGraph = new CHAAlgorithm().constructCallGraph(scene);

        // Your implementation goes here, also feel free to add methods as needed
        // To get your entry points we prepared getEntryPoints(scene) in the superclass for you

    }


    /**
     * You can use this class to represent your type assignment graph.
     * We do not use this data structure in tests, so you are free to use something else.
     * However, we use this data structure in our solution and it instantly supports collapsing strong-connected components.
     */
    private class TypeAssignmentGraph {
        private final Graph graph;
        private TarjanStronglyConnectedComponents tscc = new TarjanStronglyConnectedComponents();

        public TypeAssignmentGraph() {
            this.graph = new MultiGraph("tag");
        }

        private boolean containsNode(Value value) {
            return graph.getNode(createId(value)) != null;
        }

        private boolean containsEdge(Value source, Value target) {
            return graph.getEdge(createId(source) + "-" + createId(target)) != null;
        }

        private String createId(Value value) {
            if (value instanceof FieldRef) return value.toString();
            return Integer.toHexString(System.identityHashCode(value));
        }

        public void addNode(Value value) {
            if (!containsNode(value)) {
                Node node = graph.addNode(createId(value));
                node.setAttribute("value", value);
                node.setAttribute("ui.label", value);
                node.setAttribute("tags", new HashSet<SootClass>());
            }
        }

        public void tagNode(Value value, SootClass classTag) {
            if (containsNode(value))
                getNodeTags(value).add(classTag);
        }

        public Set<Pair<Value, Set<SootClass>>> getTaggedNodes() {
            return graph.getNodeSet().stream()
                    .map(n -> new Pair<Value, Set<SootClass>>(n.getAttribute("value"), (Set<SootClass>) n.getAttribute("tags")))
                    .filter(p -> p.second.size() > 0)
                    .collect(Collectors.toSet());
        }

        public Set<SootClass> getNodeTags(Value val) {
            return ((Set<SootClass>) graph.getNode(createId(val)).getAttribute("tags"));
        }

        public void addEdge(Value source, Value target) {
            if (!containsEdge(source, target)) {
                Node sourceNode = graph.getNode(createId(source));
                Node targetNode = graph.getNode(createId(target));
                if (sourceNode == null || targetNode == null)
                    log.error("Could not find one of the nodes. Source: " + sourceNode + " - Target: " + targetNode);
                graph.addEdge(createId(source) + "-" + createId(target),
                        sourceNode,
                        targetNode, true);
            }

        }

        public Set<Value> getTargetsFor(Value initialNode) {
            if (!containsNode(initialNode)) return Collections.emptySet();
            Node source = graph.getNode(createId(initialNode));
            Collection<Edge> edges = source.getLeavingEdgeSet();
            return edges.stream()
                    .map(e -> (Value) e.getTargetNode().getAttribute("value"))
                    .collect(Collectors.toSet());
        }

        /**
         * Use this method to start the SCC computation.
         */
        public void annotateScc() {
            tscc.init(graph);
            tscc.compute();
        }

        /**
         * Retrieve the index assigned by the SCC algorithm
         * @param value
         * @return
         */
        public Object getSccIndex(Value value) {
            if(!containsNode(value)) return null;
            return graph.getNode(createId(value)).getAttribute(tscc.getSCCIndexAttribute());
        }

        /**
         * Use this method to inspect your type assignment graph
         */
        public void draw() {
            graph.display();
        }
    }

    private class Pair<A, B> {
        final A first;
        final B second;

        public Pair(A first, B second) {
            this.first = first;
            this.second = second;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            Pair<?, ?> pair = (Pair<?, ?>) o;

            if (first != null ? !first.equals(pair.first) : pair.first != null) return false;
            return second != null ? second.equals(pair.second) : pair.second == null;
        }

        @Override
        public int hashCode() {
            int result = first != null ? first.hashCode() : 0;
            result = 31 * result + (second != null ? second.hashCode() : 0);
            return result;
        }

        @Override
        public String toString() {
            return "(" + first +
                    ", " + second +
                    ')';
        }
    }

}
