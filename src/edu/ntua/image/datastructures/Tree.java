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

public class Tree<T> {

	private TreeNode<T> rootElement;

	public Tree() {
		super();
	}

	public Tree( TreeNode<T> rootElement ) {
		setRootElement(rootElement);
	}

	public void setRootElement ( TreeNode<T> root ) {
		rootElement = root;
	}

	public TreeNode<T> getRootElement() {
		return rootElement;
	}

	public void printTree() {

		System.out.println("START");
//		Queue<Node<T>> queue = new LinkedList<Node<T>>();
		Set<TreeNode<T>> queue = new HashSet<TreeNode<T>>();
		queue.add( rootElement );
		Set<TreeNode<T>> alreadyAddedToQueue = new HashSet<TreeNode<T>>();
		Set<TreeNode<T>> alreadyPrinted = new HashSet<TreeNode<T>>();
		alreadyAddedToQueue.add( rootElement );

		while ( !queue.isEmpty() ) {
//			Node<T> cn = queue.poll();
			TreeNode<T> cn = queue.iterator().next();
			queue.remove(cn);
			if ( alreadyPrinted.contains(cn) )
				continue;
			System.out.println( cn.getNodeLabel() );
			alreadyPrinted.add( cn );
			Set<TreeNode<T>> cnChl = cn.getChildren();
			for ( TreeNode<T> nc : cnChl )
			{
				System.out.println( "\t\t" + nc.getNodeLabel() );
				if ( !alreadyAddedToQueue.contains( nc ))
				{
					queue.add( nc );
					alreadyAddedToQueue.add( nc );
				}
			}
		}
		System.out.println("END Printing tree \n");
	}
}