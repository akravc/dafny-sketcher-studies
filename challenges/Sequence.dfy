// Sequence operations and lemmas

// Helper: Reversing a sequence
function Reverse<T>(s: seq<T>): seq<T> {
    if |s| == 0 then []
    else Reverse(s[1..]) + [s[0]]
}

// Filter a sequence based on a pred
function Filter<T>(s: seq<T>, pred: T --> bool): seq<T> 
  requires forall x :: x in s ==> pred.requires(x)
{
    if |s| == 0 then []
    else if pred(s[0]) then [s[0]] + Filter(s[1..], pred)
    else Filter(s[1..], pred)
}

// Map a function over a sequence
function Map<T, U>(s: seq<T>, f: T --> U): seq<U> 
  requires forall x :: x in s ==> f.requires(x)
{
    if |s| == 0 then []
    else [f(s[0])] + Map(s[1..], f)
}

// Check if all elements satisfy a pred
function All<T>(s: seq<T>, pred: T --> bool): bool 
  requires forall x :: x in s ==> pred.requires(x)
{
    if |s| == 0 then true
    else pred(s[0]) && All(s[1..], pred)
}

// Check if a sequence is sorted (for comparable types)
function IsSorted(s: seq<int>): bool {
    if |s| <= 1 then true
    else s[0] <= s[1] && IsSorted(s[1..])
}

// Insert an element into a sorted sequence
function InsertSorted(x: int, s: seq<int>): seq<int> {
    if |s| == 0 then [x]
    else if x <= s[0] then [x] + s
    else [s[0]] + InsertSorted(x, s[1..])
}

// Sort a sequence using insertion sort
function InsertionSort(s: seq<int>): seq<int> {
    if |s| == 0 then []
    else InsertSorted(s[0], InsertionSort(s[1..]))
}

// Check if a sequence is a palindrome
function IsPalindrome<T(==)>(s: seq<T>): bool {
    s == Reverse(s)
}

// Get the maximum element in a sequence
function Max(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else var m := Max(s[1..]);
         if s[0] > m then s[0] else m
}

// Get the minimum element in a sequence
function Min(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else var m := Min(s[1..]);
         if s[0] < m then s[0] else m
}

// ===== Lemmas about Sequence operations =====

// Lemma: Reverse distributes over concatenation
lemma ReverseConcat<T>(s1: seq<T>, s2: seq<T>)
    ensures Reverse(s1 + s2) == Reverse(s2) + Reverse(s1)
{}

// Lemma: Reverse is its own inverse
lemma ReverseInvolutive<T>(s: seq<T>)
    ensures Reverse(Reverse(s)) == s
{}

// Lemma: Filter distributes over concatenation
lemma FilterConcat<T>(s1: seq<T>, s2: seq<T>, pred: T --> bool)
    requires forall x :: x in s1 + s2 ==> pred.requires(x)
    ensures Filter(s1 + s2, pred) == Filter(s1, pred) + Filter(s2, pred)
{}

// Lemma: Map distributes over concatenation
lemma MapConcat<T, U>(s1: seq<T>, s2: seq<T>, f: T --> U)
    requires forall x :: x in s1 + s2 ==> f.requires(x)
    ensures Map(s1 + s2, f) == Map(s1, f) + Map(s2, f)
{}


// Lemma: Insertion sort produces sorted sequence
lemma InsertionSortSorted(s: seq<int>)
    ensures IsSorted(InsertionSort(s))
{}

// Lemma: Insertion sort preserves length
lemma InsertionSortLength(s: seq<int>)
    ensures |InsertionSort(s)| == |s|
{}

// Lemma: Insertion sort is idempotent
lemma InsertionSortIdempotent(s: seq<int>)
    ensures InsertionSort(InsertionSort(s)) == InsertionSort(s)
{}

// Lemma: Palindrome property with concatenation
lemma PalindromeConcat<T>(s1: seq<T>, s2: seq<T>)
    requires IsPalindrome(s1) && IsPalindrome(s2)
    ensures IsPalindrome(s1 + s2) <==> s1 == Reverse(s2)
{}

// Lemma: Max and Min bounds
lemma MaxMinBounds(s: seq<int>)
    requires |s| > 0
    ensures Min(s) <= Max(s)
    ensures All(s, x => Min(s) <= x && x <= Max(s))
{}

// Lemma: Filter preserves sortedness
lemma FilterPreservesSorted(s: seq<int>, pred: int --> bool)
    requires forall x :: x in s ==> pred.requires(x)
    requires IsSorted(s)
    ensures IsSorted(Filter(s, pred))
{}


// Lemma: Complex property about sequence transformations and reversals
lemma TransformationReversal<T, U>(s: seq<T>, f: T --> U)
    requires forall x :: x in s ==> f.requires(x)
    requires forall x :: x in Reverse(s) ==> f.requires(x)
    ensures Reverse(Map(s, f)) == Map(Reverse(s), f)
{}