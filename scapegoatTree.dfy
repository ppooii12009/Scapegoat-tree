/**

  Scapegoat Tree
  Proposed by Igal Galperin and Ronald L. Rivest, 1993
  Specified and verified by Wang, September 2023

*/

/** 
  Based on vanilla binary search trees, scapegoat trees have an additional field
  `max_size`, to record the maximal value of `size(t)` since the last time the tree
  t was completely rebuilt

  In this version, we implement the delete operations using lazy deletion, so field
  `exist` is added here, to indicate if the key in this node really exists
*/
datatype Tree = Empty | Node(key: int, left: Tree, right: Tree, exist: bool)

/**
  Initiate value of constant `α`, usually 0.7 used, you can also use any arbitary
  value in [0.5, 1) 
*/
const ALPHA := 0.7

/**
  Wrap the multiply operation of real variables
*/
function multiply(a: real, b: real): (r: real)
  ensures r == a*b
{
  a * b
}

/**
  Return the maximal value between two integer values x and y
*/
function max(x: int, y: int): (r: int)
  ensures r >= x && r >= y
  ensures x > y ==> r == x
  ensures y > x ==> r == y
  ensures x == y ==> r == x == y
{
  if x > y then x else y
}

/**
  Count the size of a tree, including those lazy-deleted nodes(temporarylly marked as
  `deleted` and still exist in tree `t` until the next whole rebuilt)
*/
function size(t: Tree): (s: nat)
{
  match t
  case Empty => 0
  case Node(_, l, r, _) => size(l) + size(r) + 1
}

/**
  Count the real size of a tree, not including lazy-deleted nodes
*/
function real_size(t: Tree) : (s: nat)
  ensures s >= 0
{
  match t
  case Empty => 0
  case Node(_, l, r, e) =>
    if e then real_size(l) + real_size(r) + 1
    else real_size(l) + real_size(r)
}

/**
  Declare the h_alpha function and some basic properties
  Note: h_alpha = [log_{1/α} n]
  The origin definition of h_alpha returns an integer value using rounding operation,
  but here we remove the `.Floor` operation for two reasons:
    1: `x <= h_alpha()` implies () `x <= [h_alpha()]`
    2: we cannot give an precise mathematical implemention of logarithmic function
*/
function h_alpha(n: real, alpha: real): (r: real)
  requires 0.5 <= alpha < 1.0
  requires n > 0.0
  ensures n == 1.0 ==> h_alpha(n,alpha) == 0.0
  ensures n == alpha ==> h_alpha(n, alpha) == -1.0

/**
  Other 3 properties about h_alpha function:
    1: h_alpha increments with respect to n
    2: h_alpha increments with respect to alpha
    3: h_alpha of the product of two numbers equals the sum of the h_alpha of each number
*/
lemma h_alpha_properties()
  ensures forall m, n, alpha :: 0.5 <= alpha < 1.0 && 0.0 < m < n ==> h_alpha(m, alpha) < h_alpha(n, alpha)
  ensures forall n, alpha, alpha' :: 1.0 > alpha' > alpha >= 0.5 && n > 0.0 ==> h_alpha(n, alpha') > h_alpha(n, alpha)
  ensures forall m, n, alpha :: m > 0.0 && n > 0.0 && 0.5 <= alpha < 1.0 ==>
                                  h_alpha(m*n, alpha) == h_alpha(m, alpha) + h_alpha(n, alpha)

/**
  Wrapped version of property 3 in lemma `h_alpha_properties()`
*/
lemma h_alpha_multiply_properties(m: real, n: real, alpha: real)
  requires 0.5 <= alpha < 1.0
  requires n > 0.0
  requires m > 0.0
  ensures h_alpha(multiply(m, n), alpha) == h_alpha(multiply(n, m), alpha) == h_alpha(m, alpha) + h_alpha(n, alpha)
{
  assert h_alpha(multiply(m, n), alpha) == h_alpha(multiply(n, m), alpha) == h_alpha(m, alpha) + h_alpha(n, alpha) by{
    assert multiply(m, n) == multiply(n, m) == m*n;
    h_alpha_properties();
  }
}

/**
  Definition of alpha_weight_balanced
  Here we use `multiply()` to replace `*` to avoid non linear arithmetic logic of z3
*/
predicate alpha_weight_balanced(t: Tree, alpha: real)
  requires 0.5 <= alpha < 1.0
{
  match t
  case Empty => true
  case Node(_, l, r, _) => size(l) as real <= multiply(alpha, (size(t) as real))
                           && size(r) as real <= multiply(alpha, (size(t) as real))
                           && alpha_weight_balanced(l,alpha)
                           && alpha_weight_balanced(r,alpha)
}

/**
  Definition of alpha_height_balanced
*/
ghost predicate alpha_height_balanced(t: Tree, alpha: real)
  requires 0.5 <= alpha < 1.0
{
  match t
  case Empty => true
  case Node(_, l, r, _) =>
    tree_height(t) as real <= h_alpha(size(t) as real, alpha)
    // && alpha_height_balanced(l,alpha)
    // && alpha_height_balanced(r,alpha)
}

/**
  Definition of loose_alpha_height_balanced
*/
ghost predicate loose_alpha_height_balanced(t: Tree, alpha: real)
  requires 0.5 <= alpha < 1.0
{
  match t
  case Empty => true
  case Node(_, l, r, _) =>
    tree_height(t) as real <= h_alpha(size(t) as real, alpha) + 1.0
    // && loose_alpha_height_balanced(l,alpha)
    // && loose_alpha_height_balanced(r,alpha)
}

/**
  Collect all keys in a tree, including lazy-deleted keys
*/
function tree_elements(t: Tree): (s: set<int>)
  ensures t == Empty <==> s == {}
  ensures t != Empty ==> (forall k :: (k in tree_elements(t.left) ==> k in s) &&
                                      (k in tree_elements(t.right) ==> k in s)
                                      && t.key in s)
  ensures t != Empty ==> ( forall k :: k in s ==> (k in tree_elements(t.left))
                                                  || (k in tree_elements(t.right))
                                                  || t.key == k)
  ensures t != Empty ==>  tree_elements(t.left) <= s
                          && tree_elements(t.right) <= s
{
  match t
  case Empty => {}
  case Node(k, l, r, _) => tree_elements(l) + {k} + tree_elements(r)
}

/**
  Collect all keys in a tree without lazy-deleted keys
*/
function real_tree_elements(t: Tree): (s: set<int>)
  ensures t == Empty ==> s == {}
  ensures t != Empty ==> (forall k :: (k in real_tree_elements(t.left) ==> k in s) &&
                                      (k in real_tree_elements(t.right) ==> k in s)
                                      && (t.exist ==> t.key in s))
  ensures t != Empty ==> ( forall k :: k in s ==> (k in real_tree_elements(t.left))
                                                  || (k in real_tree_elements(t.right))
                                                  || (t.exist && t.key == k))
  ensures t != Empty ==>  real_tree_elements(t.left) <= s
                          && real_tree_elements(t.right) <= s
  ensures s <= tree_elements(t)
{
  match t
  case Empty => {}
  case Node(k, l, r, e) =>
    assert real_tree_elements(l) <= tree_elements(l);
    assert real_tree_elements(r) <= tree_elements(r);
    if e then real_tree_elements(l) + {k} + real_tree_elements(r)
    else real_tree_elements(l) + real_tree_elements(r)
}

/**
  Collect all nodes in a tree
*/
function tree_nodes(t: Tree): (s: set<Tree>)
  ensures BST(t) ==> forall n :: n in s ==> BST(n)
  ensures Empty !in s
{
  match t
  case Empty => {}
  case Node(_, l, r, _) => tree_nodes(l) + {t} + tree_nodes(r)
}

/**
  Calculate the (relative) depth of a node in the tree, starting from 0
*/
function node_depth(t: Tree, n: Tree) : (d: nat)
  requires node_in_tree(t, n)
  ensures d >= 0
{
  match t
  case Node(k, l, r, _) =>
    if n == t then 0
    else if node_in_tree(l, n) then node_depth(l, n) + 1
    else
      assert node_in_tree(r, n);
      node_depth(r, n) + 1
}

/**
  Return the node with maximal depth in the tree
*/
ghost function max_depth_node(t: Tree) : (n: Tree)
  requires tree_nodes(t) != {}
  ensures node_in_tree(t, n)
  ensures forall n' :: n' in tree_nodes(t) ==> node_depth(t, n) >= node_depth(t, n')
{
  exist_max_depth_node(t);
  var n :| n in tree_nodes(t) && (forall n' :: n' in tree_nodes(t) ==> node_depth(t, n) >= node_depth(t, n'));
  assert node_in_tree(t, n);
  n
}

/**
  Auxiliary lemma
*/
lemma exist_max_depth_node(t: Tree)
  requires tree_nodes(t) != {}
  ensures exists n :: (n in tree_nodes(t)) && (forall n' :: n' in tree_nodes(t) ==> node_depth(t, n) >= node_depth(t, n'))
{
  var A := tree_nodes(t);
  var B : set<Tree> := {};
  var n :| n in A;
  while A != {}
    decreases A
    invariant node_in_tree(t, n)
    invariant tree_nodes(t) == A + B
    invariant forall n' :: n' in B ==> node_depth(t, n') <= node_depth(t, n)
  {
    var c :| c in A;
    if node_depth(t, c) > node_depth(t, n)
    {
      n := c;
    }
    assert node_depth(t, c) <= node_depth(t, n);
    A := A - {c};
    B := B + {c};
  }
  assert A == {};
  assert B == tree_nodes(t);
  assert n in B;
  assert n in tree_nodes(t);
  assert forall n' :: n' in B ==> node_depth(t, n') <= node_depth(t, n);
}

/**
  Calculate height of a tree
  The height of a tree is the height of its root, and the height of a node is 
  the length of the longest path from that node to a leaf, which equals to the 
  maximal depth of nodes in the tree.
*/
ghost function tree_height(t: Tree) : (h: nat)
  ensures t != Empty ==> (forall n :: n in tree_nodes(t) ==> h >= node_depth(t, n))
  ensures t == Empty ==> h == 0
  ensures h == 0 <==> t == Empty || t.left == t.right == Empty
{
  match t
  case Empty => 0
  case Node(_, _, _, _) =>
    var deepest_node := max_depth_node(t);
    node_depth(t, deepest_node)
}

/**
  Recursive definition of BST(Binary-Search-Tree)
*/
predicate BST(t: Tree)
{
  match t
  case Empty => true
  case Node(k, l, r, _) => BST(l) && BST(r)
                           && (forall e :: e in tree_elements(l) ==> e < k)
                           && (forall e :: e in tree_elements(r) ==> e > k)
}

/**
  Auxiliary lemma for alpha_weight_balanced tree 
*/
lemma alpha_weight_balanced_properties(t: Tree, alpha: real)
  requires 0.5 <= alpha < 1.0
  requires alpha_weight_balanced(t, alpha)
  requires t != Empty
  ensures size(t.left) as real <= alpha*(size(t) as real)
          && size(t.right) as real <= alpha*(size(t) as real)
{
  assert size(t.left) as real <= alpha*size(t) as real by {
    assert size(t.left) as real <= multiply(alpha, size(t) as real);
    assert multiply(alpha, size(t) as real) == alpha*(size(t) as real);
  }

  assert size(t.right) as real <= alpha*size(t) as real by {
    assert size(t.right) as real <= multiply(alpha, size(t) as real);
    assert multiply(alpha, size(t) as real) == alpha*(size(t) as real);
  }
}

/**
  Some properties between balanced trees
*/
lemma{:vcs_split_on_every_assert} balanced_properties(t: Tree, alpha: real, alpha': real)
  requires 0.5 <= alpha < alpha' < 1.0
  requires BST(t)
  ensures alpha_height_balanced(t, alpha) ==> loose_alpha_height_balanced(t, alpha)
  ensures 1.0 > alpha' > alpha ==>
            (alpha_height_balanced(t, alpha) ==> alpha_height_balanced(t, alpha'))
  ensures 1.0 > alpha' > alpha ==>
            (loose_alpha_height_balanced(t, alpha) ==> loose_alpha_height_balanced(t, alpha'))
  ensures alpha_weight_balanced(t, alpha) ==> alpha_height_balanced(t, alpha)
  ensures alpha_weight_balanced(t, alpha) ==> loose_alpha_height_balanced(t, alpha)
{
  assert 1.0 > alpha' > alpha ==>
      (alpha_height_balanced(t, alpha) ==> alpha_height_balanced(t, alpha')) by {
    if alpha_height_balanced(t, alpha)
    {
      if t == Empty
      {}
      else
      {
        assert tree_height(t) as real <= h_alpha(size(t) as real, alpha);
        assert h_alpha(size(t) as real, alpha) < h_alpha(size(t) as real, alpha') by {
          h_alpha_properties();
        }
        assert tree_height(t) as real <= h_alpha(size(t) as real, alpha');
      }
    }
  }

  assert 1.0 > alpha' > alpha ==>
      (loose_alpha_height_balanced(t, alpha) ==> loose_alpha_height_balanced(t, alpha')) by {
    if loose_alpha_height_balanced(t, alpha)
    {
      if t == Empty
      {}
      else
      {
        assert tree_height(t) as real <= h_alpha(size(t) as real, alpha) + 1.0;
        assert h_alpha(size(t) as real, alpha) < h_alpha(size(t) as real, alpha') by {
          h_alpha_properties();
        }
        assert tree_height(t) as real <= h_alpha(size(t) as real, alpha') + 1.0;
      }
    }
  }

  assert alpha_height_balanced(t,alpha) ==> loose_alpha_height_balanced(t,alpha) by {
    if alpha_height_balanced(t, alpha)
    {
      if t == Empty
      {}
      else
      {
        assert tree_height(t) as real <= h_alpha(size(t) as real, alpha) + 1.0;
      }
    }
  }

  assert alpha_weight_balanced(t, alpha) ==> alpha_height_balanced(t, alpha) by {
    if alpha_weight_balanced(t, alpha)
    {
      if t == Empty
      {}
      else
      {
        assert t != Empty;
        assert alpha_height_balanced(t.left, alpha) by {
          if t.left == Empty
          {}
          else
          {
            balanced_properties(t.left, alpha, alpha + (1.0-alpha)*0.1);
          }
        }
        assert alpha_height_balanced(t.right, alpha) by {
          if t.right == Empty
          {}
          else
          {
            balanced_properties(t.right, alpha, alpha + (1.0-alpha)*0.1);
          }
        }

        assert size(t) == size(t.left) + size(t.right) + 1;
        assert tree_height(t) <= max(tree_height(t.left), tree_height(t.right)) + 1 by {
          non_empty_BST_properties(t);
        }

        assert tree_height(t) as real <= h_alpha(size(t) as real, alpha) by {
          if t.left == t.right == Empty
          {
            assert tree_height(t) == 0;
            assert size(t) == 1;
            assert h_alpha(size(t) as real, alpha) == 0.0;
          } else if t.left != Empty && t.right == Empty
          {
            assert tree_height(t.left) as real <= h_alpha(size(t.left) as real, alpha);
            assert tree_height(t) <= max(tree_height(t.left), tree_height(t.right)) + 1 == tree_height(t.left) + 1 by {
              non_empty_BST_properties(t);
            }
            assert tree_height(t) as real <= tree_height(t.left) as real + 1.0 <= h_alpha(size(t.left) as real, alpha) + 1.0
                <= h_alpha(multiply(alpha, size(t) as real), alpha) + 1.0
                == h_alpha(alpha, alpha) + h_alpha(size(t) as real, alpha) + 1.0
                == -1.0 + h_alpha(size(t) as real, alpha) + 1.0
                == h_alpha(size(t) as real, alpha) by {
              h_alpha_multiply_properties(alpha, size(t) as real, alpha);
              h_alpha_properties();
            }
          } else if t.left == Empty && t.right != Empty
          {
            assert tree_height(t.right) as real <= h_alpha(size(t.right) as real, alpha);
            assert tree_height(t) <= max(tree_height(t.left), tree_height(t.right)) + 1 == tree_height(t.right) + 1 by {
              non_empty_BST_properties(t);
            }
            assert tree_height(t) as real <= tree_height(t.right) as real + 1.0 <= h_alpha(size(t.right) as real, alpha) + 1.0
                <= h_alpha(multiply(alpha, size(t) as real), alpha) + 1.0
                == h_alpha(alpha, alpha) + h_alpha(size(t) as real, alpha) + 1.0
                == -1.0 + h_alpha(size(t) as real, alpha) + 1.0
                == h_alpha(size(t) as real, alpha) by {
              h_alpha_multiply_properties(alpha, size(t) as real, alpha);
              h_alpha_properties();
            }
          } else
          {
            assert t.left != Empty && t.right != Empty;
            assert tree_height(t) <= max(tree_height(t.left), tree_height(t.right)) + 1 by {
              non_empty_BST_properties(t);
            }
            assert tree_height(t.left) as real + 1.0 <= h_alpha(size(t.left) as real, alpha) + 1.0
                <= h_alpha(multiply(alpha, size(t) as real), alpha) + 1.0
                == h_alpha(alpha, alpha) + h_alpha(size(t) as real, alpha) + 1.0
                == -1.0 + h_alpha(size(t) as real, alpha) + 1.0
                == h_alpha(size(t) as real, alpha) by {
              h_alpha_multiply_properties(alpha, size(t) as real, alpha);
              h_alpha_properties();
            }
            assert tree_height(t.right) as real + 1.0 <= h_alpha(size(t.right) as real, alpha) + 1.0
                <= h_alpha(multiply(alpha, size(t) as real), alpha) + 1.0
                == h_alpha(alpha, alpha) + h_alpha(size(t) as real, alpha) + 1.0
                == -1.0 + h_alpha(size(t) as real, alpha) + 1.0
                == h_alpha(size(t) as real, alpha) by {
              h_alpha_multiply_properties(alpha, size(t) as real, alpha);
              h_alpha_properties();
            }
          }
        }
        assert alpha_height_balanced(t, alpha);
      }
    }
  }
}

/**
  To indicate that a tree remains its height after lazy-deletion
*/
lemma tree_flip_existence_remains_height(t: Tree, t': Tree)
  requires BST(t)
  requires BST(t')
  requires t != Empty && t' != Empty
  requires t.left == t'.left && t.right == t'.right
  ensures tree_height(t) == tree_height(t')
{
  assert tree_nodes(t') == tree_nodes(t'.left) + tree_nodes(t'.right) + {t'};
  assert tree_nodes(t) == tree_nodes(t.left) + tree_nodes(t.right) + {t};
  assert tree_nodes(t') == tree_nodes(t.left) + tree_nodes(t.right) + {t'};

  assert t !in tree_nodes(t.left) && t !in tree_nodes(t.right) by {
    non_empty_BST_properties(t);
  }
  assert t' !in tree_nodes(t'.left) && t' !in tree_nodes(t'.right) by {
    non_empty_BST_properties(t');
  }

  assert tree_nodes(t') == tree_nodes(t) - {t} + {t'};

  assert tree_nodes(t.left) * tree_nodes(t.right) == {} by {
    non_empty_BST_properties(t);
  }

  assert forall n :: n in tree_nodes(t'.left) ==> n in tree_nodes(t.left);
  assert forall n :: n in tree_nodes(t'.right) ==> n in tree_nodes(t.right);

  assert forall n :: n in tree_nodes(t.left) ==> node_in_tree(t', n) && node_in_tree(t'.left, n);
  assert forall n :: n in tree_nodes(t.right) ==> node_in_tree(t', n) && node_in_tree(t'.right, n);

  assert forall n :: n in tree_nodes(t.left) ==> node_depth(t'.left, n) == node_depth(t.left, n);
  assert forall n :: n in tree_nodes(t.right) ==> node_depth(t'.right, n) == node_depth(t.right, n);

  assert forall n :: n in tree_nodes(t.left) ==> node_depth(t, n) == node_depth(t.left, n) + 1;
  assert forall n :: n in tree_nodes(t.right) ==> node_depth(t, n) == node_depth(t.right, n) + 1;

  assert forall n :: n in tree_nodes(t.left) ==> node_depth(t', n) == node_depth(t'.left, n) + 1;
  assert forall n :: n in tree_nodes(t.right) ==> node_depth(t', n) == node_depth(t'.right, n) + 1;

  assert forall n :: n in tree_nodes(t.left) ==> node_depth(t, n) == node_depth(t', n);
  assert forall n :: n in tree_nodes(t.right) ==> node_depth(t, n) == node_depth(t', n);

  assert forall n :: n in tree_nodes(t.left) || n in tree_nodes(t.right) ==> node_depth(t, n) == node_depth(t', n);
}

/**
  Determine if a node is in the tree
*/
predicate node_in_tree(t: Tree, n: Tree)
{
  if n == Empty then false
  else n in tree_nodes(t)
}

/**
  Two same trees share the same element set
*/
lemma equal_properties(p: Tree, q: Tree)
  requires p == q
  ensures tree_elements(p) == tree_elements(q)
  ensures real_tree_elements(p) == real_tree_elements(q)
{
}

/**
  Propetries about node and the tree it is in
*/
lemma node_properties(t: Tree, n: Tree)
  requires BST(t)
  requires BST(n)
  ensures t != Empty && t == n ==> node_in_tree(t, n)
  ensures
    match t
    case Empty => node_in_tree(t, n) == false
    case Node(k, l, r, _) =>
      match n
      case Empty => node_in_tree(t, n) == false
      case Node(k', _, _, _) =>
        if t == n then  node_in_tree(t, n) == true
                        && k' in tree_elements(t)
        else node_in_tree(t, n) == node_in_tree(l, n) || node_in_tree(r, n)
  ensures node_in_tree(t, n) == true ==> tree_elements(n) <= tree_elements(t)
  ensures node_in_tree(t, n) == true ==> real_tree_elements(n) <= real_tree_elements(t)
  ensures node_in_tree(t, n) == true ==> n != Empty && t != Empty
{
}

/**
  Trivial properties hold for all trees(including non-BSTs)
*/
lemma ordinary_tree_properties(t: Tree)
  ensures real_tree_elements(t) <= tree_elements(t)
  ensures (forall n :: n in tree_nodes(t) ==> n.exist) ==> real_tree_elements(t) == tree_elements(t)
  ensures t != Empty ==> node_in_tree(t, t)
  ensures real_tree_elements(t) <= tree_elements(t)
{
}

/**
  The number of nodes equals the number of elements for BSTs
*/
lemma BST_properties(t: Tree)
  requires BST(t)
  ensures |tree_nodes(t)| == |tree_elements(t)|
  ensures |tree_nodes(t)| == size(t)
{
  assert |tree_nodes(t)| == |tree_elements(t)| by {
    if t == Empty
    {
      assert tree_nodes(t) == {};
      assert tree_elements(t) == {};
    }
    else
    {
      non_empty_BST_properties(t);
      var n :| n in tree_nodes(t);
      tree_node_matches_tree_element(t, n);
      var k :| k in tree_elements(t);
      tree_element_matches_tree_node(t, k);
    }
  }

  assert |tree_nodes(t)| == size(t) by
  {
    if t == Empty
    {
      assert tree_nodes(t) == {};
      assert size(t) == 0;
    }
    else
    {
      non_empty_BST_properties(t);
      assert |tree_nodes(t.left)| == size(t.left) by {
        BST_properties(t.left);
      }
      assert |tree_nodes(t.right)| == size(t.right) by {
        BST_properties(t.right);
      }
      assert |tree_nodes(t)| == |tree_nodes(t.left)| + 1 + |tree_nodes(t.right)|;
      assert size(t) == size(t.left) + 1 + size(t.right);
      assert |tree_nodes(t)| == size(t);
    }
  }
}

/**
  Most of the auxiliary lemma for non-empty BSTs are here, so attribute
  `:vcs_split_on_every_assert` is used here for acceleration of proof
  Note: when `:vcs_split_on_every_assert` is used, the proof process may "succeed"
    in advance(usually in several seconds), but only all the gutter status change 
    to solid green bars does the proof process really ends successfully
*/
lemma{:vcs_split_on_every_assert} non_empty_BST_properties(t: Tree)
  requires BST(t)
  requires t != Empty
  ensures tree_elements(t.left) * tree_elements(t.right) == {}
  ensures real_tree_elements(t.left) * real_tree_elements(t.right) == {}
  ensures tree_elements(t.left) + {t.key} + tree_elements(t.right) == tree_elements(t)
  ensures t.exist ==>
            real_tree_elements(t.left) + {t.key} + real_tree_elements(t.right) == real_tree_elements(t)
  ensures !t.exist ==>
            real_tree_elements(t.left) + real_tree_elements(t.right) == real_tree_elements(t)
  ensures t.left != Empty ==> node_in_tree(t, t.left)
  ensures t.right != Empty ==> node_in_tree(t, t.right)
  ensures (forall e :: e in real_tree_elements(t.left) ==> e < t.key)
          && (forall e :: e in real_tree_elements(t.right) ==> e > t.key)
  ensures t !in tree_nodes(t.left)
  ensures t !in tree_nodes(t.right)
  ensures tree_nodes(t.left) * tree_nodes(t.right) == {}
  ensures t.left != Empty || t.right != Empty ==> tree_height(t) == max(tree_height(t.left), tree_height(t.right)) + 1
{
  assert t !in tree_nodes(t.left) by {
    if(t in tree_nodes(t.left))
    {
      assert t != Empty;
      assert node_in_tree(t.left, t);
      assert tree_elements(t) <= tree_elements(t.left) by {
        node_properties(t.left, t);
      }
      assert t.key in tree_elements(t.left);
    }
  }
  assert t !in tree_nodes(t.right) by {
    if(t in tree_nodes(t.right))
    {
      assert t != Empty;
      assert node_in_tree(t.right, t);
      assert tree_elements(t) <= tree_elements(t.right) by {
        node_properties(t.right, t);
      }
      assert t.key in tree_elements(t.right);
    }
  }
  assert tree_nodes(t.left) * tree_nodes(t.right) == {} by {
    match t.left
    case Empty =>
      assert tree_nodes(t.left) == {};
      assert {} * tree_nodes(t.right) == {};
    case Node(_, _, _, _) =>
      assert tree_nodes(t.left) != {};
      if tree_nodes(t.left) * tree_nodes(t.right) != {}
      {
        var n :| n in tree_nodes(t.left) && n in tree_nodes(t.right);
        tree_node_matches_tree_element(t.right, n);
        tree_node_matches_tree_element(t.left, n);
        assert n.key in tree_elements(t.right);
        assert n.key in tree_elements(t.left);
        assert n.key > t.key && n.key < t.key;
      }
  }

  assert t.left != Empty || t.right != Empty ==> tree_height(t) == max(tree_height(t.left), tree_height(t.right)) + 1 by {
    assert  forall n :: n in tree_nodes(t.left) ==>
                          node_depth(t, n) == node_depth(t.left, n) + 1;
    assert  forall n :: n in tree_nodes(t.right) ==>
                          node_depth(t, n) == node_depth(t.right, n) + 1;
    assert tree_nodes(t) == tree_nodes(t.left) + tree_nodes(t.right) + {t};
    assert node_depth(t, t) == 0;
  }
}

/**
  Auxiliary lemma
*/
lemma tree_node_matches_tree_element(t: Tree, n: Tree)
  requires BST(t)
  requires node_in_tree(t, n)
  ensures n.key in tree_elements(t)
{}

/**
  Auxiliary lemma
*/
lemma tree_element_matches_tree_node(t: Tree, k: int)
  requires BST(t)
  requires k in tree_elements(t)
  ensures exists n :: n in tree_nodes(t) && n.key == k
{}

/**
  Search if a key exists in the tree
  For lazy-deleted keys, the predicate will return false
 */
predicate search(t: Tree, x: int)
  requires BST(t)
  ensures search(t, x) == true <==> x in real_tree_elements(t)
{
  match t
  case Empty => false
  case Node(k, l, r, e) =>
    if k == x then e
    else if x < k then search(l, x)
    else search(r, x)
}

/**
  Insert a key into a tree recursively
 */
ghost function{:vcs_split_on_every_assert} insert_key(t: Tree, x: int) : (t': Tree)
  requires BST(t)
  ensures BST(t')
  ensures tree_elements(t') == tree_elements(t) + {x}
  ensures real_tree_elements(t') == real_tree_elements(t) + {x}
{
  match t
  case Empty =>
    assert BST(Node(x, Empty, Empty, true));
    assert tree_elements(t) == {};
    assert tree_elements(Node(x, Empty, Empty, true)) == tree_elements(t) + {x};
    assert real_tree_elements(t) == {};
    assert real_tree_elements(Node(x, Empty, Empty, true)) == real_tree_elements(t) + {x};
    Node(x, Empty, Empty, true)
  case Node(k, l, r, e) =>
    if x < k then
      assert BST(l);
      assert BST(insert_key(l, x));
      assert BST(Node(k, insert_key(l, x), r, e));
      Node(k, insert_key(l, x), r, e)
    else if x > k then
      assert BST(r);
      assert BST(insert_key(r, x));
      assert BST(Node(k, l, insert_key(r, x), e));
      Node(k, l, insert_key(r, x), e)
    else
      assert BST(t);
      assert BST(Node(k, l, r, true));
      assert tree_elements(t) == tree_elements(t) + {x};
      assert e ==> real_tree_elements(t) == real_tree_elements(t) + {x};
      assert !e ==> real_tree_elements(Node(k, l, r, true)) == real_tree_elements(t) + {x};
      if e then t
      else
        Node(k, l, r, true)
}

/**
  Insert a key into a tree
  This function does insertion operation in two steps:
    1: insert the key into the tree
      if some node contains the key, then turn its `exist` field to `true`
      if not, add a new node recursively
    2: balance the tree using `balance_tree`
 */
ghost function{:vcs_split_on_every_assert} insert(t: Tree, x: int) : (t': Tree)
  requires BST(t)
  requires loose_alpha_height_balanced(t, ALPHA)
  ensures BST(t')
  ensures tree_elements(t') == tree_elements(t) + {x}
  ensures real_tree_elements(t') == real_tree_elements(t) + {x}
  ensures loose_alpha_height_balanced(t', ALPHA)
{
  match t
  case Empty =>
    assert BST(Node(x, Empty, Empty, true));
    assert tree_elements(t) == {};
    assert tree_elements(Node(x, Empty, Empty, true)) == tree_elements(t) + {x};
    assert real_tree_elements(t) == {};
    assert real_tree_elements(Node(x, Empty, Empty, true)) == real_tree_elements(t) + {x};
    assert loose_alpha_height_balanced(Node(x, Empty, Empty, true), ALPHA);
    Node(x, Empty, Empty, true)
  case Node(k, l, r, e) =>
    var t' := insert_key(t, x);
    if loose_alpha_height_balanced(t', ALPHA) then t'
    else balance_tree(t')
}

/**
  Lazy-deletion of key `x` in tree `t`
  This function does not guarantee the balance property. So this is a mid-operation.
 */
function delete_key(t: Tree, x: int) : (t': Tree)
  requires BST(t)
  ensures BST(t')
  ensures tree_elements(t) == tree_elements(t')
  ensures search(t, x) <==> real_tree_elements(t) == real_tree_elements(t') + {x}
  ensures real_tree_elements(t) - {x} == real_tree_elements(t')
  ensures x !in real_tree_elements(t')
{
  match t
  case Empty => Empty
  case Node(k, l, r, e) =>
    if k == x then Node(k, l, r, false)
    else if x < k then Node(k, delete_key(l, x), r, e)
    else Node(k, l, delete_key(r, x), e)
}

/**
  Complete delete function implemention
  This function does (lazy-)deletion operation in two steps:
    1: lazy delete the key from tree using `delete_key`
    2: wholely rebuild the tree if too many nodes are lazy deleted(`real_size` 
      is too small with respect to ALPHA*`size`)
 */
ghost function delete(t: Tree, x: int) : (t': Tree)
  requires loose_alpha_height_balanced(t, ALPHA)
  requires BST(t)
  ensures BST(t')
  ensures real_tree_elements(t) - {x} == real_tree_elements(t')
  ensures search(t, x) <==> real_tree_elements(t) == real_tree_elements(t') + {x}
  ensures x !in real_tree_elements(t')
  ensures loose_alpha_height_balanced(t, ALPHA)
{
  match t
  case Empty => Empty
  case Node(_, _, _, _) =>
    var tmp := delete_key(t, x);
    if real_size(tmp) as real < ALPHA*(size(tmp) as real) then whole_rebuild(tmp)
    else tmp
}

/**
  Check if a sequence is sorted in ascending order
 */
predicate sorted(s: seq<int>)
{
  forall i,j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

/**
  Check if a sequence does not contain duplicate elements
 */
predicate unique_elements(s: seq<int>)
{
  forall i,j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

/**
  Auxiliary function for insertion sort
 */
function insort(a: int, s: seq<int>): (r: seq<int>)
  requires sorted(s)
  ensures a in r
  ensures forall x :: x in s ==> x in r
  ensures multiset(r) == multiset{a} + multiset(s)
  ensures sorted(r)
{
  if s == [] then [a]
  else if a <= s[0] then
    assert s == [s[0]] + s[1..];
    [a] + s
  else
    assert s == [s[0]] + s[1..];
    assert forall x :: x in insort(a, s[1..]) ==> x in multiset(insort(a, s[1..])) ==> x in multiset(s[1..]) || x in multiset{a};
    assert forall x :: x in insort(a, s[1..]) ==> x in s[1..] || x in {a};
    [s[0]] + insort(a, s[1..])
}

/**
  Sort a sequence
 */
function insertion_sort(s: seq<int>): (r: seq<int>)
  ensures multiset(s) == multiset(r)
  ensures sorted(r)
  ensures forall x :: x in s ==> x in r
  ensures |s| == |r|
{
  if s == [] then []
  else
    var rest := insertion_sort(s[1..]);
    assert s == [s[0]] + s[1..];
    insort(s[0], rest)
}

/**
  Convert a set to sequence
 */
ghost function set_to_sequence(s: set<int>) : (r: seq<int>)
  ensures multiset(s) == multiset(r)
  ensures |s| == |r|
  ensures unique_elements(r)
{
  if s == {} then []
  else
    var x :| x in s;
    assert x !in s-{x};
    assert x !in multiset(s-{x});
    assert forall i :: 0 <= i < |set_to_sequence(s-{x})| ==> set_to_sequence(s-{x})[i] != x;
    [x] + set_to_sequence(s-{x})
}

/**
  Build a tree with specified elements
 */
ghost function{:vcs_split_on_every_assert} build_tree(s: seq<int>) : (t: Tree)
  requires sorted(s)
  requires unique_elements(s)
  ensures multiset(tree_elements(t)) == multiset(s)
  ensures forall n :: n in tree_nodes(t) ==> n.exist
  ensures tree_elements(t) == real_tree_elements(t)
  ensures BST(t)
  ensures alpha_weight_balanced(t, 0.5)
{
  if s == [] then
    assert BST(Empty);
    assert tree_elements(Empty) == {};
    assert multiset(s) == multiset{};
    assert multiset(tree_elements(Empty)) == multiset(s);
    assert real_tree_elements(Empty) == {};
    assert alpha_weight_balanced(Empty, 0.5);
    Empty
  else
    var mid := |s| / 2;
    var key := s[mid];
    var lseq := s[..mid];
    var rseq := s[mid+1..];
    var l := build_tree(lseq);
    var r := build_tree(rseq);
    assert s == lseq + [key] + rseq;
    assert forall k :: k in lseq ==> k < key;
    assert forall k :: k in rseq ==> k > key;
    assert multiset(tree_elements(l)) == multiset(lseq);
    assert multiset(tree_elements(r)) == multiset(rseq);
    assert seq_disjoint(lseq,rseq);
    assert seq_disjoint(lseq,[key]);
    assert seq_disjoint(rseq,[key]);
    assert multiset_disjoint(multiset(lseq),multiset(rseq));
    assert multiset_disjoint(multiset(lseq),multiset{key});
    assert multiset_disjoint(multiset(rseq),multiset{key});
    assert multiset_disjoint(multiset(tree_elements(l)),multiset(tree_elements(r)));
    assert multiset_disjoint(multiset(tree_elements(l)),multiset{key});
    assert multiset_disjoint(multiset(tree_elements(l)),multiset{key});
    assert set_disjoint(tree_elements(l),{key});
    assert set_disjoint(tree_elements(r),{key});
    assert set_disjoint(tree_elements(l),tree_elements(r));
    assert multiset(lseq)!!multiset(rseq);
    assert multiset(lseq)!!multiset{key};
    assert multiset(rseq)!!multiset{key};
    assert multiset(tree_elements(l))!!multiset(tree_elements(r));
    assert tree_elements(l)!!tree_elements(r);
    assert tree_elements(l)!!{key};
    assert tree_elements(r)!!{key};
    assert multiset(s) == multiset(lseq) + multiset{key} + multiset(rseq);
    assert  tree_elements(Node(key, l, r, true)) ==
            tree_elements(l) + tree_elements(r) + {key};
    assert  multiset(tree_elements(Node(key, l, r, true))) ==
            multiset(tree_elements(l)) + multiset(tree_elements(r)) + multiset{key};

    assert forall k :: k in tree_elements(l) ==> k < key by {
      assert multiset(tree_elements(l)) == multiset(lseq);
      multiset_properties(tree_elements(l),lseq,key);
      assert (forall k :: k in tree_elements(l) ==> k < key) <==> (forall k' :: k' in lseq ==> k' < key);
      assert forall k' :: k' in lseq ==> k' < key;
    }

    assert forall k :: k in tree_elements(r) ==> k > key by {
      assert multiset(tree_elements(r)) == multiset(rseq);
      multiset_properties(tree_elements(r),rseq,key);
      assert (forall k :: k in tree_elements(r) ==> k > key) <==> (forall k' :: k' in rseq ==> k' > key);
      assert forall k' :: k' in rseq ==> k' > key;
    }

    assert BST(l);
    assert BST(r);
    assert BST(Node(key, l, r, true)) by {
      assert forall k :: k in tree_elements(l) ==> k < key;
      assert forall k :: k in tree_elements(r) ==> k > key;
      assert BST(l);
      assert BST(r);
    }

    assert alpha_weight_balanced(l, 0.5);
    assert alpha_weight_balanced(r, 0.5);
    assert size(Node(key, l, r, true)) == size(l) + size(r) + 1;
    assert |tree_elements(l)| == |tree_nodes(l)| by {
      BST_properties(l);
    }
    assert |tree_elements(r)| == |tree_nodes(r)| by {
      BST_properties(r);
    }
    assert |tree_elements(l)| <= |tree_elements(r)| + 1;
    assert |tree_elements(r)| <= |tree_elements(l)| + 1;
    assert |tree_nodes(l)| <= |tree_nodes(r)| + 1;
    assert |tree_nodes(r)| <= |tree_nodes(l)| + 1;
    assert |tree_nodes(l)| == size(l) by {
      BST_properties(l);
    }
    assert |tree_nodes(r)| == size(r) by {
      BST_properties(r);
    }
    assert size(l) <= size(r) + 1;
    assert size(r) <= size(l) + 1;
    assert alpha_weight_balanced(Node(key, l, r, true), 0.5);

    Node(key, l, r, true)
}

/**
  Auxiliary lemma
 */
lemma multiset_properties(s: set<int>, q: seq<int>, v: int)
  requires multiset(s) == multiset(q)
  ensures (forall k :: k in s ==> k < v) <==> (forall k' :: k' in multiset(s) ==> k' < v)
  ensures (forall k :: k in s ==> k > v) <==> (forall k' :: k' in multiset(s) ==> k' > v)
  ensures (forall k :: k in s ==> k in q) && (forall k :: k in q ==> k in s)
  ensures (forall k :: k in s ==> k < v) <==> (forall k' :: k' in q ==> k' < v)
  ensures (forall k :: k in s ==> k > v) <==> (forall k' :: k' in q ==> k' > v)
{
  assert forall k :: k in s ==> k in multiset(s);
  assert forall k :: k in multiset(s) ==> k in s;
  assert forall k :: k in q ==> k in multiset(q);
  assert forall k :: k in multiset(q) ==> k in q;
  assert forall k :: k in s ==> k in q;
  assert forall k :: k in q ==> k in s;
  assert (forall k :: k in s ==> k < v) <==> (forall k' :: k' in multiset(s) ==> k' < v);
  assert (forall k :: k in s ==> k > v) <==> (forall k' :: k' in multiset(s) ==> k' > v);
}

/**
  Auxiliary lemma
 */
lemma multiset_disjointness_properties(s1: set<int>, s2: set<int>, s3: set<int>)
  requires s1!!s2
  requires s1!!s3
  requires s2!!s3
  ensures multiset(s1+s2+s3) == multiset(s1) + multiset(s2) + multiset(s3)
{
}

/**
  Auxiliary lemma
 */
lemma set_equal_equivalence_multiset_equal(s1: set<int>, s2: set<int>)
  ensures s1 == s2 <==> multiset(s1) == multiset(s2)
{
  assert forall k :: k in multiset(s1) ==> k in s1;
  assert forall k :: k in multiset(s2) ==> k in s2;
}

/**
  Auxiliary lemma
 */
lemma unique_elements_implies_multiplicity_equals_1(s: seq<int>)
  requires unique_elements(s)
  ensures forall k :: k in multiset(s) ==> multiset(s)[k] == 1
{
  var ms := multiset(s);
  if !(forall k :: k in ms ==> ms[k] == 1)
  {
    var k :| k in ms && ms[k] > 1;
    var i :| 0 < i < |s|;
    var left := s[..i];
    var right := s[i..];
    assert s == left+right;
    // assert multiset(s) == multiset(left) + multiset(right);
    // assert multiset(s)[k] == multiset(left)[k] + multiset(right)[k];
    if k in left && k in right
    {
      assert !unique_elements(s);
    } else if k in left && k !in right
    {
      unique_elements_implies_multiplicity_equals_1(left);
    } else if k !in left && k in right
    {
      unique_elements_implies_multiplicity_equals_1(right);
    }else
    {
      assert k !in multiset(s);
    }
  }
}

/**
  Auxiliary lemma
 */
lemma multiplicity_equals_1_implies_unique_elements(s: seq<int>)
  requires forall k :: k in multiset(s) ==> multiset(s)[k] == 1
  ensures unique_elements(s)
{
  if(!unique_elements(s))
  {
    var i, j, k :| 0 <= i < j < |s| && s[i] == s[j] == k;
    var left := s[..i+1];
    var right := s[i+1..];
    assert s == left + right;
    assert j >= i+1;
    assert k in left && k in right;
    assert multiset(s)[k] >= 2;
  }
}

/**
  Auxiliary lemma
 */
lemma unique_elements_equivalence(s: seq<int>)
  ensures unique_elements(s) <==> forall k :: k in multiset(s) ==> multiset(s)[k] == 1
{
  if(unique_elements(s))
  {
    unique_elements_implies_multiplicity_equals_1(s);
  }
  if(forall k :: k in multiset(s) ==> multiset(s)[k] == 1)
  {
    multiplicity_equals_1_implies_unique_elements(s);
  }
}

/**
  Auxiliary lemma
 */
lemma sequence_properties(s: seq<int>, r: seq<int>)
  requires unique_elements(s)
  requires multiset(s) == multiset(r)
  ensures unique_elements(r)
{
  unique_elements_equivalence(s);
  unique_elements_equivalence(r);
}

/**
  Determine if two multisets are disjoint
 */
predicate multiset_disjoint(s1: multiset<int>, s2: multiset<int>)
  ensures multiset_disjoint(s1,s2) <==> s1!!s2
{
  (forall k :: k in s1 ==> k !in s2) && (forall k :: k in s2 ==> k !in s1)
}

/**
  Determine if two sequences are disjoint
 */
predicate seq_disjoint(s1: seq<int>, s2: seq<int>)
  ensures seq_disjoint(s1,s2) <==> multiset_disjoint(multiset(s1),multiset(s2))
  ensures seq_disjoint(s1,s2) <==> multiset(s1)!!multiset(s2)
{
  assert forall k :: k in s1 <==> k in multiset(s1);
  (forall k :: k in s1 ==> k !in s2) && (forall k :: k in s2 ==> k !in s1)
}

/**
  Determine if two sets are disjoint
 */
predicate set_disjoint(s1: set<int>, s2: set<int>)
  ensures set_disjoint(s1,s2) <==> multiset_disjoint(multiset(s1),multiset(s2))
  ensures set_disjoint(s1,s2) <==> s1!!s2
  ensures set_disjoint(s1,s2) <==> multiset(s1)!!multiset(s2)
{
  assert forall k :: k in s1 <==> k in multiset(s1);
  (forall k :: k in s1 ==> k !in s2) && (forall k :: k in s2 ==> k !in s1)
}

/**
  Whole rebuild a tree recursively
  After rebuilt, all the nodes(keys) that have been lazy-deleted before will be 
  real-deleted. And this process ensures the new tree is 0.5-weight-balanced(
  since it uses `build_tree`, and `build_tree` ensures it)
 */
ghost function{:vcs_split_on_every_assert} whole_rebuild(t: Tree) : (t': Tree)
  requires BST(t)
  ensures BST(t')
  ensures real_tree_elements(t) == real_tree_elements(t')
  ensures tree_elements(t') == real_tree_elements(t')
{
  var elements := real_tree_elements(t);
  assert unique_elements(set_to_sequence(elements));
  var sorted_elements := insertion_sort(set_to_sequence(elements));
  assert multiset(set_to_sequence(elements)) == multiset(sorted_elements);
  assert |set_to_sequence(elements)| == |sorted_elements|;
  assert unique_elements(sorted_elements) by {
    sequence_properties(set_to_sequence(elements),sorted_elements);
  }
  var new_tree := build_tree(sorted_elements);
  assert BST(new_tree);
  assert tree_elements(new_tree) == real_tree_elements(new_tree);
  assert multiset(real_tree_elements(new_tree)) == multiset(sorted_elements);
  assert multiset(elements) == multiset(sorted_elements);
  assert multiset(real_tree_elements(new_tree)) == multiset(real_tree_elements(t));
  assert real_tree_elements(t) == real_tree_elements(new_tree) by {
    assert multiset(real_tree_elements(new_tree)) == multiset(real_tree_elements(t));
    set_equal_equivalence_multiset_equal(real_tree_elements(new_tree),real_tree_elements(t));
  }
  new_tree
}

/**
  Part implemention of function `balance_tree`
  Balance the tree to 0.5-alpha-weight(height)-balanced, and ensures the set of 
  real elements equals to `s`
 */
ghost function{:vcs_split_on_every_assert} correct_key(t: Tree, s: set<int>) : (t': Tree)
  requires BST(t)
  requires s <= tree_elements(t)
  requires alpha_weight_balanced(t, 0.5)
  ensures BST(t')
  ensures alpha_weight_balanced(t', 0.5)
  ensures loose_alpha_height_balanced(t', ALPHA)
  ensures tree_elements(t) == tree_elements(t')
  ensures real_tree_elements(t') == s
  ensures size(t) == size(t')
{
  match t
  case Empty => Empty
  case Node(k, l, r, e) =>
    var ls := set x | x in s && x < k;
    var rs := set x | x in s && x > k;
    if k !in s
    then
      assert ls + rs == s;
      var l' := correct_key(l, ls);
      var r' := correct_key(r, rs);
      var t' := Node(k, l', r', false);

      assert size(l') == size(l);
      assert size(r') == size(r);
      assert size(t) == size(t');
      assert alpha_weight_balanced(t', 0.5);
      assert loose_alpha_height_balanced(t', ALPHA) by {
        balanced_properties(t', 0.5, ALPHA);
      }
      t'
    else
      assert k in s;
      assert ls + rs + {k} == s;
      var l' := correct_key(l, ls);
      var r' := correct_key(r, rs);
      var t' := Node(k, l', r', true);

      assert size(l') == size(l);
      assert size(r') == size(r);
      assert size(t) == size(t');
      assert alpha_weight_balanced(t', 0.5);
      assert loose_alpha_height_balanced(t', ALPHA) by {
        balanced_properties(t', 0.5, ALPHA);
      }
      t'
}

/**
  Complete balance operation
  This function balance the tree in two steps:
    1: build a new 0.5-weight-balanced tree with the same tree elements
    2: adjust the newly built tree using `correct_key` to ensure the set of 
    real elements keeps the same as before
 */
ghost function{:vcs_split_on_every_assert} balance_tree(t: Tree) : (t': Tree)
  requires BST(t)
  ensures BST(t')
  ensures loose_alpha_height_balanced(t', ALPHA)
  ensures tree_elements(t) == tree_elements(t')
  ensures real_tree_elements(t) == real_tree_elements(t')
{
  var element_set := tree_elements(t);
  var element_seq := set_to_sequence(element_set);
  var sorted_element_seq := insertion_sort(element_seq);
  assert unique_elements(sorted_element_seq) by {
    sequence_properties(element_seq, sorted_element_seq);
  }
  var t0 := build_tree(sorted_element_seq);
  assert alpha_weight_balanced(t0, 0.5);
  assert alpha_height_balanced(t0, 0.5) by {
    balanced_properties(t0, 0.5, ALPHA);
  }
  assert loose_alpha_height_balanced(t0, 0.5) by {
    balanced_properties(t0, 0.5, ALPHA);
  }
  assert loose_alpha_height_balanced(t0, ALPHA) by {
    balanced_properties(t0, 0.5, ALPHA);
  }
  assert multiset(tree_elements(t0)) == multiset(sorted_element_seq)
      == multiset(element_seq) == multiset(element_set);
  assert tree_elements(t0) == tree_elements(t) by {
    set_equal_equivalence_multiset_equal(tree_elements(t0), tree_elements(t));
  }
  correct_key(t0, real_tree_elements(t))
}
