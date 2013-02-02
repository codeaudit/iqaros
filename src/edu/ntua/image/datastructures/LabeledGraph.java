/*
 * #%L
 * IQAROS
 *
 * $Id$
 * $HeadURL$
 * %%
 * Copyright (C) 2011 by the Image, Video and Multimedia Laboratory, NTUA
 * %%
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 * #L%
 */

package edu.ntua.image.datastructures;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

public class LabeledGraph<VerticesType,VerticeLabelType,EdgeLabelType> {

	public class Edge {
		protected VerticesType toElement;
		protected EdgeLabelType edgeLabel;

		public Edge( EdgeLabelType label, VerticesType to ){
	        edgeLabel = label;
	        toElement = to;
		}
		public VerticesType getToElement(){
			return toElement;
		}
		public EdgeLabelType getEdgeLabel(){
			return edgeLabel;
		}
		@Override
		public String toString(){
			return edgeLabel + " " + toElement;
		}
	}

    protected final Set<VerticesType> elements;
    protected final Map<VerticesType,Set<VerticeLabelType>> labelsByNodes;
    protected final Map<VerticesType,Set<EdgeLabelType>> edgeLabelsByNodes;
    protected final Map<VerticesType,Set<Edge>> successorsByNodes;
    protected final Map<VerticesType,Set<Edge>> predecessorsByNodes;

    public LabeledGraph() {
        elements = new HashSet<VerticesType>();
        labelsByNodes = new HashMap<VerticesType,Set<VerticeLabelType>>();
        edgeLabelsByNodes = new HashMap<VerticesType,Set<EdgeLabelType>>();
        successorsByNodes = new HashMap<VerticesType,Set<Edge>>();
        predecessorsByNodes = new HashMap<VerticesType,Set<Edge>>();

    }
    public void addLabel(VerticesType node, VerticeLabelType nodeLabel){
    	Set<VerticeLabelType> nodeLabels = labelsByNodes.get( node );
		if( nodeLabels == null ){
			nodeLabels = new HashSet<VerticeLabelType>();
			labelsByNodes.put(node , nodeLabels);
		}
		nodeLabels.add(nodeLabel);
		elements.add(node);
    }
    public Set<VerticeLabelType> getLabelsOfNode(VerticesType node){
    	Set<VerticeLabelType> labelsOfNode = labelsByNodes.get( node );
    	if( labelsOfNode == null )
    		labelsOfNode = Collections.emptySet();
    	return labelsOfNode;
    }
    public Set<EdgeLabelType> getAllLabelsOfOutgoingEdges(VerticesType node){
    	return edgeLabelsByNodes.get( node );
    }
    public void addEdge(VerticesType from, VerticesType to, EdgeLabelType label) {
        Set<Edge> successorEdges = successorsByNodes.get(from);
        if (successorEdges == null) {
        	successorEdges = new HashSet<Edge>();
            successorsByNodes.put(from, successorEdges);
        }
        Edge newEdge = new Edge(label, to);
        successorEdges.add(newEdge);

        Set<Edge> predecessorEdges = predecessorsByNodes.get(to);
        if (predecessorEdges == null) {
        	predecessorEdges = new HashSet<Edge>();
        	predecessorsByNodes.put(to, predecessorEdges);
        }
        Edge newEdgeInverse = new Edge(label, from);
        predecessorEdges.add(newEdgeInverse);

        Set<EdgeLabelType> edgeLabels = edgeLabelsByNodes.get(from);
        if (edgeLabels == null) {
        	edgeLabels = new HashSet<EdgeLabelType>();
        	edgeLabelsByNodes.put(from, edgeLabels);
        }
        edgeLabels.add(label);

        elements.add(from);
        elements.add(to);
    }
    public Set<VerticesType> getElements() {
        return elements;
    }
    public boolean hasCycles(){
		for( VerticesType var : elements )
			if( isReachableSuccessor( var, var ) )
				return true;
		return false;
	}
    public void invertEdge( VerticesType from, Edge edge, EdgeLabelType invertedEdgeLabel ){
    	successorsByNodes.get( from ).remove( edge );
    	addEdge( edge.getToElement(), from, invertedEdgeLabel );
    }
    public boolean isReachableSuccessor(VerticesType fromNode,VerticesType toNode) {
//	    	if( fromNode.equals( toNode ))
//	    		return true;
        Set<VerticesType> result = new HashSet<VerticesType>();
        Queue<VerticesType> toVisit=new LinkedList<VerticesType>();
        toVisit.add(fromNode);
        while (!toVisit.isEmpty()) {
        	VerticesType current=toVisit.poll();
        	Set<Edge> successorEdges = getSuccessors( current );
            if( containsToNode( successorEdges , toNode ) )
            	return true;
            if( result.add(current) )
                toVisit.addAll( getAllToNodes( successorEdges ) );
        }
        return false;
    }
    private Set<VerticesType> getAllToNodes(Set<Edge> successorEdges) {
    	Set<VerticesType> allToNodes = new HashSet<VerticesType>();
    	for( Edge edge : successorEdges )
    		allToNodes.add( edge.getToElement() );
		return allToNodes;
	}
	private boolean containsToNode(Set<Edge> successorEdges, VerticesType toNode) {
		for( Edge edge : successorEdges )
			if( edge.getToElement().equals( toNode ))
				return true;
		return false;
	}
	public Set<Edge> getSuccessors(VerticesType node) {
        Set<Edge> result = successorsByNodes.get(node);
        if (result==null)
            result=Collections.emptySet();
        return result;
    }
	public Set<Edge> getPredecessors(VerticesType node) {
        Set<Edge> result = predecessorsByNodes.get(node);
        if (result==null)
            result=Collections.emptySet();
        return result;
    }
    @Override
	public LabeledGraph<VerticesType,VerticeLabelType,EdgeLabelType> clone() {
    	LabeledGraph<VerticesType,VerticeLabelType,EdgeLabelType> result=new LabeledGraph<VerticesType,VerticeLabelType,EdgeLabelType>();
        for (Map.Entry<VerticesType,Set<Edge>> entry : successorsByNodes.entrySet()) {
            VerticesType from=entry.getKey();
            for (Edge successor : entry.getValue())
                result.addEdge(from,successor.getToElement(),successor.getEdgeLabel());
        }
        return result;
    }
	public void printGraph(){
		for( VerticesType var : getElements() ){
			System.out.println( "current var is: " + var  + " with label: " + getLabelsOfNode(var) );
			for( Edge edge : getSuccessors( var ) )
				System.out.println( "successor var is " + edge.getToElement() + " with edge label: " + edge.getEdgeLabel() );
			for( Edge edge : getPredecessors( var ) )
				System.out.println( "predecessor var is " + edge.getToElement() + " with edge label: " + edge.getEdgeLabel() );

			System.out.println( );
		}
	}
}