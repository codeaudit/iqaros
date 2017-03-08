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

import java.util.HashSet;
import java.util.Set;
import java.util.Stack;

public class TreeNode<T> {

	public T nodeLabel;
	public Set<TreeNode<T>> children;

	public TreeNode() {
		super();
	}

	public TreeNode( T clause ) {
		this();
		setNodeLabel( clause );
	}

	public Set<TreeNode<T>> getChildren() {
		if ( children == null )
			return new HashSet<TreeNode<T>>();
		return children;
	}

	public void setChildren( Set<TreeNode<T>> child ) {
		children = child;
	}

	public void addChild( TreeNode<T> child ) {
		if ( children == null )
			children = new HashSet<TreeNode<T>>();
		children.add( child );
	}

	public void removeChild( TreeNode<T> child ) {
		children.remove( child );
	}

	public void setNodeLabel( T clause ) {
		this.nodeLabel = clause;
	}

	public T getNodeLabel() {
		return this.nodeLabel;
	}

	public Set<TreeNode<T>> getSubTree() {
		Set<TreeNode<T>> list = new HashSet<TreeNode<T>>();
		Stack<TreeNode<T>> stack = new Stack<TreeNode<T>>();
		stack.add(this);
		while (!stack.isEmpty()) {
			TreeNode<T> current = stack.pop();
			list.add(current);
			stack.addAll(current.getChildren());
		}
		return list;
	}

//	public Set<T> getSubTreeAsSet() {
//		Set<T> list = new HashSet<T>();
//		walk(this, list);
//		return list;
//	}
//
//	private void walk(Node<T> element, Set<T> list) {
//		list.add(element.getNodeLabel());
//       for (Node<T> data : element.getChildren()) {
//       	walk(data, list);
//       }
//	}
//
	public Set<T> getSubTreeAsSet() {
		Set<T> list = new HashSet<T>();
		Stack<TreeNode<T>> stack = new Stack<TreeNode<T>>();
		Set<TreeNode<T>> alreadyAdded = new HashSet<TreeNode<T>>();
//		alreadyAdded.add( this );
		stack.add(this);
		while (!stack.isEmpty()) {
			TreeNode<T> current = stack.pop();
			list.add(current.getNodeLabel());
			alreadyAdded.add( current );
			for ( TreeNode<T> n : current.getChildren() )
				if ( !alreadyAdded.contains( n ) )
					stack.add( n );
		}
		return list;
	}

	public void addChildren(Set<TreeNode<T>> set) {
		if ( children == null )
			children = new HashSet<TreeNode<T>>();
		children.addAll(set);
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof TreeNode) {
			TreeNode<T> o = (TreeNode<T>) obj;

    		return this.getNodeLabel().toString().equals(o.getNodeLabel().toString());
    	}
    	return false;
    }

    @Override
	public int hashCode() {
    	int i = 0;
    	return this.getNodeLabel().hashCode();
    }
}
