package analysis;

import soot.SootMethod;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

public class CallGraph {
    public final String algorithm;
    private final Set<SootMethod> nodes;
    private final Set<Edge<SootMethod, SootMethod>> edges;

    public CallGraph(String algorithm) {
        this.algorithm = algorithm;

        nodes = new HashSet<SootMethod>();
        edges = new HashSet<Edge<SootMethod, SootMethod>>();
    }

    public CallGraph(String algorithm, CallGraph cg) {
        this(algorithm);

        nodes.addAll(cg.nodes);
        edges.addAll(cg.edges);
    }

    public void addNode(SootMethod method) {
        if (nodes.contains(method))
            throw new IllegalArgumentException("Call graph already contains method: " + method.toString());
        nodes.add(method);
    }

    public void addEdge(SootMethod source, SootMethod target) {
        if (!nodes.contains(source))
            throw new IllegalArgumentException("Call graph does not contain source node. Please add source node first. " + source.toString());
        if (!nodes.contains(target))
            throw new IllegalArgumentException("Call graph does not contain target node. Please add target node first. " + target.toString());

        Edge<SootMethod, SootMethod> edge = new Edge<>(source, target);
        if (edges.contains(edge))
            throw new IllegalArgumentException("Call graph already contains edge: " + edge.toString());

        edges.add(edge);
    }

    public boolean hasNode(SootMethod m) {
        return nodes.contains(m);
    }
    public boolean hasEdge(SootMethod source, SootMethod target) { return edges.contains(new Edge<>(source, target));}

    public Set<SootMethod> edgesOutOf(SootMethod origin) {
        if (!nodes.contains(origin)) return Collections.emptySet();

        return edges.stream().filter(edge -> edge.source.equals(origin))
                      .map(edge -> edge.target)
                      .collect(Collectors.toSet());
    }

    public Set<SootMethod> edgesInto(SootMethod target) {
        if (!nodes.contains(target)) return Collections.emptySet();

        return edges.stream().filter(edge -> edge.target.equals(target))
                .map(edge -> edge.source)
                .collect(Collectors.toSet());
    }
}
