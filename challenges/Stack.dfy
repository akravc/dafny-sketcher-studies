// Stack implementation in Dafny with interesting lemmas
// This implementation uses a sequence to represent the stack

datatype Stack<T> = Stack(contents: seq<T>)

// Constructor for empty stack
function EmptyStack<T>(): Stack<T> {
    Stack([])
}

// Check if stack is empty
function IsEmpty<T>(s: Stack<T>): bool {
    |s.contents| == 0
}

// Push an element onto the stack
function Push<T>(s: Stack<T>, x: T): Stack<T> {
    Stack([x] + s.contents)
}

// Pop an element from the stack
function Pop<T>(s: Stack<T>): (Stack<T>, T)
    requires !IsEmpty(s)
{
    (Stack(s.contents[1..]), s.contents[0])
}

// Peek at the top element without removing it
function Peek<T>(s: Stack<T>): T
    requires !IsEmpty(s)
{
    s.contents[0]
}

// Get the size of the stack
function Size<T>(s: Stack<T>): nat {
    |s.contents|
}

// Convert stack to sequence (for verification purposes)
function ToSeq<T>(s: Stack<T>): seq<T> {
    s.contents
}

// Pushing all elements of a sequence onto the stack
function FoldPush<T>(s: Stack<T>, elements: seq<T>): Stack<T> 
  decreases |elements|
{
    if |elements| == 0 then s
    else FoldPush(Push(s, elements[0]), elements[1..])
}

// Helper: Reversing a sequence
function Reverse<T>(s: seq<T>): seq<T> {
    if |s| == 0 then []
    else Reverse(s[1..]) + [s[0]]
}

// Lemma: Stack reversal property
// If we push elements in order and then pop them all, we get them in reverse order
lemma StackReversalProperty<T>(s: Stack<T>, elements: seq<T>)
    ensures ToSeq(FoldPush(s, elements)) == Reverse(elements) + ToSeq(s)
{}


// Lemma: Multiple push associativity
// The order of pushing multiple elements doesn't matter for the final result
lemma PushAssociativity<T>(s: Stack<T>, x: T, y: T, z: T)
    ensures Push(Push(Push(s, x), y), z) == Push(Push(Push(s, z), y), x)
{}

// Helper function: Pop multiple elements
function PopMultiple<T>(s: Stack<T>, count: nat): (Stack<T>, seq<T>)
    requires count <= Size(s)
    decreases count
{
    if count == 0 then (s, [])
    else var (s', x) := Pop(s);
         var (s'', xs) := PopMultiple(s', count - 1);
         (s'', [x] + xs)
}

// Lemma: Size preservation through push-pop operations
// If we push n elements and then pop n elements, the size remains unchanged
lemma SizePreservation<T>(s: Stack<T>, elements: seq<T>)
    requires |elements| <= Size(s)
    ensures Size(FoldPush(s, elements)) == 
            Size(PopMultiple(FoldPush(s, elements), |elements|).0)
{}


// Lemma: Stack concatenation property
// Concatenating two stacks preserves the LIFO property
lemma StackConcatenation<T>(s1: Stack<T>, s2: Stack<T>)
  requires Size(s2) <= Size(FoldPush(s1, ToSeq(s2)))
  ensures var combined := FoldPush(s1, ToSeq(s2));
          var (result, _) := PopMultiple(combined, Size(s2));
          result == s1
{}


// Lemma: Complex stack transformation
// Pushing elements in reverse order and then reversing the stack gives original order
lemma ComplexTransformation<T>(s: Stack<T>, elements: seq<T>)
  requires |elements| <= Size(FoldPush(s, Reverse(elements)))
    ensures var reversed := FoldPush(s, Reverse(elements));
            var (result, _) := PopMultiple(reversed, |elements|);
            ToSeq(result) == ToSeq(s)
{}

// Lemma: Stack transformation invariance
// Certain transformations preserve stack properties
lemma TransformationInvariance<T>(s: Stack<T>, elements: seq<T>)
    requires |elements| > 0
    requires 0 < Size(FoldPush(s, elements))
    ensures var s' := FoldPush(s, elements);
            var (s'', _) := Pop(s');
            Size(s'') == Size(s) + |elements| - 1
{}


// Lemma: Stack composition property
// Composing multiple stack operations can be optimized
lemma StackComposition<T>(s: Stack<T>, elements1: seq<T>, elements2: seq<T>)
    ensures var s1 := FoldPush(s, elements1);
            var s2 := FoldPush(s1, elements2);
            var s3 := FoldPush(s, elements1 + elements2);
            s2 == s3
{}