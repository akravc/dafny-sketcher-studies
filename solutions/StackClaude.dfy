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

// Helper lemma: Reverse preserves length
lemma ReversePreservesLength<T>(s: seq<T>)
    ensures |Reverse(s)| == |s|
    decreases |s|
{
    if |s| == 0 {
        assert Reverse(s) == [];
        assert |Reverse(s)| == 0 == |s|;
    } else {
        var rest := s[1..];
        ReversePreservesLength(rest);
        assert |Reverse(rest)| == |rest|;
        assert Reverse(s) == Reverse(rest) + [s[0]];
        assert |Reverse(s)| == |Reverse(rest)| + 1 == |rest| + 1 == |s|;
    }
}

// Lemma: Stack reversal property
// If we push elements in order and then pop them all, we get them in reverse order
lemma StackReversalProperty<T>(s: Stack<T>, elements: seq<T>)
    ensures ToSeq(FoldPush(s, elements)) == Reverse(elements) + ToSeq(s)
    decreases |elements|
{
    if |elements| == 0 {
        // Base case: empty sequence
        assert FoldPush(s, elements) == s;
        assert Reverse(elements) == [];
        assert ToSeq(FoldPush(s, elements)) == ToSeq(s);
        assert Reverse(elements) + ToSeq(s) == [] + ToSeq(s) == ToSeq(s);
    } else {
        // Inductive case
        var first := elements[0];
        var rest := elements[1..];
        
        // By definition of FoldPush
        assert FoldPush(s, elements) == FoldPush(Push(s, first), rest);
        
        // Apply inductive hypothesis
        StackReversalProperty(Push(s, first), rest);
        assert ToSeq(FoldPush(Push(s, first), rest)) == Reverse(rest) + ToSeq(Push(s, first));
        
        // Expand ToSeq(Push(s, first))
        assert ToSeq(Push(s, first)) == [first] + ToSeq(s);
        
        // So we have ToSeq(FoldPush(s, elements)) == Reverse(rest) + [first] + ToSeq(s)
        
        // By definition of Reverse
        assert Reverse(elements) == Reverse(rest) + [first];
        
        // Therefore: Reverse(elements) + ToSeq(s) == (Reverse(rest) + [first]) + ToSeq(s)
        //                                          == Reverse(rest) + [first] + ToSeq(s)
        //                                          == ToSeq(FoldPush(s, elements))
    }
}


// Lemma: Push operation associativity with sequences
// Pushing elements as a sequence vs individually gives the same result
lemma PushAssociativity<T>(s: Stack<T>, x: T, y: T, z: T)
    ensures Push(Push(Push(s, x), y), z) == FoldPush(s, [x, y, z])
{
    // Push(Push(Push(s, x), y), z) creates a stack with contents [z, y, x] + s.contents
    // FoldPush(s, [x, y, z]) should create the same result
    
    // Let's trace through FoldPush step by step:
    // FoldPush(s, [x, y, z]) = FoldPush(Push(s, x), [y, z])
    //                        = FoldPush(Push(Push(s, x), y), [z])
    //                        = FoldPush(Push(Push(Push(s, x), y), z), [])
    //                        = Push(Push(Push(s, x), y), z)
    
    assert FoldPush(s, [x, y, z]) == FoldPush(Push(s, x), [y, z]);
    assert FoldPush(Push(s, x), [y, z]) == FoldPush(Push(Push(s, x), y), [z]);
    assert FoldPush(Push(Push(s, x), y), [z]) == Push(Push(Push(s, x), y), z);
}

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
    ensures Size(FoldPush(s, elements)) == Size(s) + |elements|
    ensures Size(s) + |elements| >= |elements| ==> 
            Size(PopMultiple(FoldPush(s, elements), |elements|).0) == Size(s)
{
    // First, prove that FoldPush increases size by the number of elements
    FoldPushSizeHelper(s, elements);
    
    // Second, prove that PopMultiple decreases size correctly
    if Size(s) + |elements| >= |elements| {
        PopMultipleSizeHelper(FoldPush(s, elements), |elements|);
    }
}

// Helper lemma: FoldPush increases size by the number of elements added
lemma FoldPushSizeHelper<T>(s: Stack<T>, elements: seq<T>)
    ensures Size(FoldPush(s, elements)) == Size(s) + |elements|
    decreases |elements|
{
    if |elements| == 0 {
        assert FoldPush(s, elements) == s;
        assert Size(FoldPush(s, elements)) == Size(s);
        assert Size(s) + |elements| == Size(s) + 0 == Size(s);
    } else {
        var first := elements[0];
        var rest := elements[1..];
        
        // By definition of FoldPush
        assert FoldPush(s, elements) == FoldPush(Push(s, first), rest);
        
        // Size of Push(s, first) is Size(s) + 1
        assert Size(Push(s, first)) == Size(s) + 1;
        
        // Apply inductive hypothesis
        FoldPushSizeHelper(Push(s, first), rest);
        assert Size(FoldPush(Push(s, first), rest)) == Size(Push(s, first)) + |rest|;
        assert Size(FoldPush(s, elements)) == (Size(s) + 1) + |rest|;
        assert |elements| == 1 + |rest|;
        assert Size(FoldPush(s, elements)) == Size(s) + |elements|;
    }
}

// Helper lemma: PopMultiple decreases size by the number of elements popped
lemma PopMultipleSizeHelper<T>(s: Stack<T>, count: nat)
    requires count <= Size(s)
    ensures Size(PopMultiple(s, count).0) == Size(s) - count
    decreases count
{
    if count == 0 {
        assert PopMultiple(s, count) == (s, []);
        assert PopMultiple(s, count).0 == s;
        assert Size(PopMultiple(s, count).0) == Size(s);
        assert Size(s) - count == Size(s) - 0 == Size(s);
    } else {
        var (s', x) := Pop(s);
        var (s'', xs) := PopMultiple(s', count - 1);
        
        assert PopMultiple(s, count) == (s'', [x] + xs);
        assert PopMultiple(s, count).0 == s'';
        
        // Size after one pop
        assert Size(s') == Size(s) - 1;
        
        // Apply inductive hypothesis
        assert count - 1 <= Size(s');
        PopMultipleSizeHelper(s', count - 1);
        assert Size(s'') == Size(s') - (count - 1);
        assert Size(s'') == (Size(s) - 1) - (count - 1);
        assert Size(s'') == Size(s) - count;
    }
}


// Lemma: Stack concatenation property
// Concatenating two stacks preserves the LIFO property
lemma StackConcatenation<T>(s1: Stack<T>, s2: Stack<T>)
  ensures var combined := FoldPush(s1, ToSeq(s2));
          Size(s2) <= Size(combined) &&
          var (result, popped) := PopMultiple(combined, Size(s2));
          result == s1 && popped == Reverse(ToSeq(s2))
{
    var combined := FoldPush(s1, ToSeq(s2));
    
    // First, establish the size relationship
    FoldPushSizeHelper(s1, ToSeq(s2));
    assert Size(combined) == Size(s1) + |ToSeq(s2)|;
    assert |ToSeq(s2)| == Size(s2);
    assert Size(combined) == Size(s1) + Size(s2);
    assert Size(s2) <= Size(combined);
    
    var (result, popped) := PopMultiple(combined, Size(s2));
    
    // Use our stack reversal property
    StackReversalProperty(s1, ToSeq(s2));
    assert ToSeq(combined) == Reverse(ToSeq(s2)) + ToSeq(s1);
    
    // Now prove the PopMultiple behavior
    StackConcatenationHelper(s1, s2);
}

// Helper lemma for stack concatenation
lemma StackConcatenationHelper<T>(s1: Stack<T>, s2: Stack<T>)
    ensures var combined := FoldPush(s1, ToSeq(s2));
            Size(s2) <= Size(combined) &&
            var (result, popped) := PopMultiple(combined, Size(s2));
            result == s1 && popped == Reverse(ToSeq(s2))
{
    var combined := FoldPush(s1, ToSeq(s2));
    
    // First establish that Size(s2) <= Size(combined)
    FoldPushSizeHelper(s1, ToSeq(s2));
    assert Size(combined) == Size(s1) + |ToSeq(s2)|;
    assert |ToSeq(s2)| == Size(s2);
    assert Size(combined) == Size(s1) + Size(s2);
    assert Size(s2) <= Size(combined);
    
    // We know from StackReversalProperty that:
    // ToSeq(combined) == Reverse(ToSeq(s2)) + ToSeq(s1)
    StackReversalProperty(s1, ToSeq(s2));
    
    // Now we need to show that PopMultiple takes exactly the right elements
    // The combined stack has contents: Reverse(ToSeq(s2)) + ToSeq(s1)
    // PopMultiple should take the first Size(s2) elements, which are exactly Reverse(ToSeq(s2))
    ReversePreservesLength(ToSeq(s2));
    assert |Reverse(ToSeq(s2))| == |ToSeq(s2)| == Size(s2);
    PopMultipleFromConcatenatedHelper(Reverse(ToSeq(s2)), ToSeq(s1), Size(s2));
}

// Helper lemma for popping from concatenated sequences
lemma PopMultipleFromConcatenatedHelper<T>(prefix: seq<T>, suffix: seq<T>, count: nat)
    requires count == |prefix|
    ensures var s := Stack(prefix + suffix);
            var (result, popped) := PopMultiple(s, count);
            ToSeq(result) == suffix && popped == prefix
{
    if count == 0 {
        assert prefix == [];
        var s := Stack(prefix + suffix);
        assert s == Stack(suffix);
        var (result, popped) := PopMultiple(s, count);
        assert (result, popped) == (s, []);
        assert ToSeq(result) == suffix && popped == prefix;
    } else {
        assert |prefix| > 0;
        var first := prefix[0];
        var prefixRest := prefix[1..];
        
        var s := Stack(prefix + suffix);
        assert s.contents == [first] + (prefixRest + suffix);
        
        var (s', x) := Pop(s);
        assert x == first;
        assert ToSeq(s') == prefixRest + suffix;
        
        var (result, poppedRest) := PopMultiple(s', count - 1);
        
        // Apply inductive hypothesis
        assert count - 1 == |prefixRest|;
        PopMultipleFromConcatenatedHelper(prefixRest, suffix, count - 1);
        assert ToSeq(result) == suffix && poppedRest == prefixRest;
        
        var (finalResult, finalPopped) := PopMultiple(s, count);
        assert finalResult == result && finalPopped == [x] + poppedRest;
        assert ToSeq(finalResult) == suffix && finalPopped == [first] + prefixRest == prefix;
    }
}


// Lemma: Complex stack transformation
// Pushing elements in reverse order and then reversing the stack gives original order
lemma ComplexTransformation<T>(s: Stack<T>, elements: seq<T>)
    ensures var reversed := FoldPush(s, Reverse(elements));
            |elements| <= Size(reversed) &&
            var (result, popped) := PopMultiple(reversed, |elements|);
            ToSeq(result) == ToSeq(s) && popped == elements
{
    var reversed := FoldPush(s, Reverse(elements));
    
    // First establish the size relationship
    FoldPushSizeHelper(s, Reverse(elements));
    assert Size(reversed) == Size(s) + |Reverse(elements)|;
    ReversePreservesLength(elements);
    assert |Reverse(elements)| == |elements|;  // Reverse preserves length
    assert Size(reversed) == Size(s) + |elements|;
    assert |elements| <= Size(reversed);
    
    var (result, popped) := PopMultiple(reversed, |elements|);
    
    // Use the stack reversal property
    StackReversalProperty(s, Reverse(elements));
    assert ToSeq(reversed) == Reverse(Reverse(elements)) + ToSeq(s);
    
    // Prove that Reverse(Reverse(elements)) == elements
    ReverseReverseIdentity(elements);
    assert Reverse(Reverse(elements)) == elements;
    assert ToSeq(reversed) == elements + ToSeq(s);
    
    // Apply the concatenated popping helper
    assert |elements| == |elements|;
    PopMultipleFromConcatenatedHelper(elements, ToSeq(s), |elements|);
    assert ToSeq(result) == ToSeq(s) && popped == elements;
}

// Helper lemma: Double reverse is identity
lemma ReverseReverseIdentity<T>(s: seq<T>)
    ensures Reverse(Reverse(s)) == s
{
    if |s| == 0 {
        assert Reverse(s) == [];
        assert Reverse(Reverse(s)) == Reverse([]) == [];
        assert s == [];
    } else {
        var first := s[0];
        var rest := s[1..];
        
        // Reverse(s) = Reverse(rest) + [first]
        assert Reverse(s) == Reverse(rest) + [first];
        
        // Reverse(Reverse(s)) = Reverse(Reverse(rest) + [first])
        //                     = Reverse([first]) + Reverse(Reverse(rest))    (by reverse concatenation property)
        //                     = [first] + Reverse(Reverse(rest))             (since Reverse([first]) = [first])
        //                     = [first] + rest                                (by inductive hypothesis)
        //                     = s
        
        // Apply inductive hypothesis
        ReverseReverseIdentity(rest);
        assert Reverse(Reverse(rest)) == rest;
        
        // Apply reverse concatenation property
        ReverseConcatenationProperty(Reverse(rest), [first]);
        assert Reverse(Reverse(rest) + [first]) == Reverse([first]) + Reverse(Reverse(rest));
        assert Reverse([first]) == [first];
        assert Reverse(Reverse(s)) == [first] + rest == s;
    }
}

// Helper lemma: Reverse distributes over concatenation (in reverse order)
lemma ReverseConcatenationProperty<T>(s1: seq<T>, s2: seq<T>)
    ensures Reverse(s1 + s2) == Reverse(s2) + Reverse(s1)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
        assert Reverse(s1) == [];
        assert Reverse(s1 + s2) == Reverse(s2);
        assert Reverse(s2) + Reverse(s1) == Reverse(s2) + [] == Reverse(s2);
    } else {
        var first := s1[0];
        var rest := s1[1..];
        
        assert s1 == [first] + rest;
        assert s1 + s2 == [first] + (rest + s2);
        
        // Reverse(s1 + s2) = Reverse([first] + (rest + s2))
        //                  = Reverse(rest + s2) + [first]
        assert Reverse(s1 + s2) == Reverse(rest + s2) + [first];
        
        // Apply inductive hypothesis
        ReverseConcatenationProperty(rest, s2);
        assert Reverse(rest + s2) == Reverse(s2) + Reverse(rest);
        
        // So Reverse(s1 + s2) = (Reverse(s2) + Reverse(rest)) + [first]
        //                     = Reverse(s2) + (Reverse(rest) + [first])
        //                     = Reverse(s2) + Reverse([first] + rest)
        //                     = Reverse(s2) + Reverse(s1)
        assert Reverse(s1 + s2) == Reverse(s2) + (Reverse(rest) + [first]);
        assert Reverse(rest) + [first] == Reverse([first] + rest) == Reverse(s1);
        assert Reverse(s1 + s2) == Reverse(s2) + Reverse(s1);
    }
}

// Lemma: Stack transformation invariance
// Certain transformations preserve stack properties
lemma TransformationInvariance<T>(s: Stack<T>, elements: seq<T>)
    requires |elements| > 0
    ensures var s' := FoldPush(s, elements);
            !IsEmpty(s') && 
            var (s'', _) := Pop(s');
            Size(s'') == Size(s) + |elements| - 1
{
    var s' := FoldPush(s, elements);
    
    // First establish the size of s' after FoldPush
    FoldPushSizeHelper(s, elements);
    assert Size(s') == Size(s) + |elements|;
    
    // Since |elements| > 0, we have Size(s') > Size(s) >= 0
    assert Size(s') > 0;
    assert !IsEmpty(s');
    
    var (s'', top) := Pop(s');
    
    // After popping one element, the size decreases by 1
    assert Size(s'') == Size(s') - 1;
    assert Size(s'') == (Size(s) + |elements|) - 1;
    assert Size(s'') == Size(s) + |elements| - 1;
}


// Lemma: Stack composition property
// Composing multiple stack operations can be optimized
lemma StackComposition<T>(s: Stack<T>, elements1: seq<T>, elements2: seq<T>)
    ensures var s1 := FoldPush(s, elements1);
            var s2 := FoldPush(s1, elements2);
            var s3 := FoldPush(s, elements1 + elements2);
            s2 == s3
{
    var s1 := FoldPush(s, elements1);
    var s2 := FoldPush(s1, elements2);
    var s3 := FoldPush(s, elements1 + elements2);
    
    // We need to prove that s2 == s3
    // s2 = FoldPush(FoldPush(s, elements1), elements2)
    // s3 = FoldPush(s, elements1 + elements2)
    
    // This follows from the fact that FoldPush is associative with respect to concatenation
    FoldPushConcatenationProperty(s, elements1, elements2);
    assert s2 == s3;
}

// Helper lemma: FoldPush distributes over sequence concatenation
lemma FoldPushConcatenationProperty<T>(s: Stack<T>, elements1: seq<T>, elements2: seq<T>)
    ensures FoldPush(FoldPush(s, elements1), elements2) == FoldPush(s, elements1 + elements2)
    decreases |elements1|
{
    if |elements1| == 0 {
        assert FoldPush(s, elements1) == s;
        assert FoldPush(FoldPush(s, elements1), elements2) == FoldPush(s, elements2);
        assert elements1 + elements2 == [] + elements2 == elements2;
        assert FoldPush(s, elements1 + elements2) == FoldPush(s, elements2);
    } else {
        var first := elements1[0];
        var rest := elements1[1..];
        
        // FoldPush(s, elements1) = FoldPush(Push(s, first), rest)
        assert FoldPush(s, elements1) == FoldPush(Push(s, first), rest);
        
        // So FoldPush(FoldPush(s, elements1), elements2) = FoldPush(FoldPush(Push(s, first), rest), elements2)
        var s_with_first := Push(s, first);
        var s1 := FoldPush(s_with_first, rest);
        assert FoldPush(s, elements1) == s1;
        assert FoldPush(FoldPush(s, elements1), elements2) == FoldPush(s1, elements2);
        
        // Apply inductive hypothesis to rest and elements2
        FoldPushConcatenationProperty(s_with_first, rest, elements2);
        assert FoldPush(s1, elements2) == FoldPush(s_with_first, rest + elements2);
        assert FoldPush(FoldPush(s, elements1), elements2) == FoldPush(s_with_first, rest + elements2);
        
        // For the other side: FoldPush(s, elements1 + elements2)
        assert elements1 + elements2 == [first] + (rest + elements2);
        assert FoldPush(s, elements1 + elements2) == FoldPush(Push(s, first), rest + elements2);
        assert FoldPush(s, elements1 + elements2) == FoldPush(s_with_first, rest + elements2);
        
        // Therefore they are equal
        assert FoldPush(FoldPush(s, elements1), elements2) == FoldPush(s, elements1 + elements2);
    }
}