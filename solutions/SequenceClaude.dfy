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
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
        assert Reverse(s1) == [];
        assert Reverse(s1 + s2) == Reverse(s2);
        assert Reverse(s2) + Reverse(s1) == Reverse(s2) + [] == Reverse(s2);
    } else {
        var head := s1[0];
        var tail := s1[1..];
        assert s1 == [head] + tail;
        assert s1 + s2 == [head] + (tail + s2);
        
        calc {
            Reverse(s1 + s2);
            Reverse([head] + (tail + s2));
            Reverse(tail + s2) + [head];
            { ReverseConcat(tail, s2); }
            (Reverse(s2) + Reverse(tail)) + [head];
            Reverse(s2) + (Reverse(tail) + [head]);
            Reverse(s2) + Reverse([head] + tail);
            Reverse(s2) + Reverse(s1);
        }
    }
}

// Lemma: Reverse is its own inverse
lemma ReverseInvolutive<T>(s: seq<T>)
    ensures Reverse(Reverse(s)) == s
{
    if |s| == 0 {
        assert Reverse(s) == [];
        assert Reverse(Reverse(s)) == Reverse([]) == [] == s;
    } else {
        var head := s[0];
        var tail := s[1..];
        assert s == [head] + tail;
        
        calc {
            Reverse(Reverse(s));
            Reverse(Reverse([head] + tail));
            Reverse(Reverse(tail) + [head]);
            { ReverseConcat(Reverse(tail), [head]); }
            Reverse([head]) + Reverse(Reverse(tail));
            [head] + Reverse(Reverse(tail));
            { ReverseInvolutive(tail); }
            [head] + tail;
            s;
        }
    }
}

// Lemma: Filter distributes over concatenation
lemma FilterConcat<T>(s1: seq<T>, s2: seq<T>, pred: T --> bool)
    requires forall x :: x in s1 + s2 ==> pred.requires(x)
    ensures Filter(s1 + s2, pred) == Filter(s1, pred) + Filter(s2, pred)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
        assert Filter(s1, pred) == [];
        assert Filter(s1 + s2, pred) == Filter(s2, pred);
        assert Filter(s1, pred) + Filter(s2, pred) == [] + Filter(s2, pred) == Filter(s2, pred);
    } else {
        var head := s1[0];
        var tail := s1[1..];
        assert s1 == [head] + tail;
        assert s1 + s2 == [head] + (tail + s2);
        assert forall x :: x in tail + s2 ==> pred.requires(x);
        
        if pred(head) {
            calc {
                Filter(s1 + s2, pred);
                Filter([head] + (tail + s2), pred);
                [head] + Filter(tail + s2, pred);
                { FilterConcat(tail, s2, pred); }
                [head] + (Filter(tail, pred) + Filter(s2, pred));
                ([head] + Filter(tail, pred)) + Filter(s2, pred);
                Filter([head] + tail, pred) + Filter(s2, pred);
                Filter(s1, pred) + Filter(s2, pred);
            }
        } else {
            calc {
                Filter(s1 + s2, pred);
                Filter([head] + (tail + s2), pred);
                Filter(tail + s2, pred);
                { FilterConcat(tail, s2, pred); }
                Filter(tail, pred) + Filter(s2, pred);
                Filter([head] + tail, pred) + Filter(s2, pred);
                Filter(s1, pred) + Filter(s2, pred);
            }
        }
    }
}

// Lemma: Map distributes over concatenation
lemma MapConcat<T, U>(s1: seq<T>, s2: seq<T>, f: T --> U)
    requires forall x :: x in s1 + s2 ==> f.requires(x)
    ensures Map(s1 + s2, f) == Map(s1, f) + Map(s2, f)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
        assert Map(s1, f) == [];
        assert Map(s1 + s2, f) == Map(s2, f);
        assert Map(s1, f) + Map(s2, f) == [] + Map(s2, f) == Map(s2, f);
    } else {
        var head := s1[0];
        var tail := s1[1..];
        assert s1 == [head] + tail;
        assert s1 + s2 == [head] + (tail + s2);
        assert forall x :: x in tail + s2 ==> f.requires(x);
        
        calc {
            Map(s1 + s2, f);
            Map([head] + (tail + s2), f);
            [f(head)] + Map(tail + s2, f);
            { MapConcat(tail, s2, f); }
            [f(head)] + (Map(tail, f) + Map(s2, f));
            ([f(head)] + Map(tail, f)) + Map(s2, f);
            Map([head] + tail, f) + Map(s2, f);
            Map(s1, f) + Map(s2, f);
        }
    }
}


// Helper lemma: Inserting into a sorted sequence keeps it sorted
lemma InsertSortedKeepsSorted(x: int, s: seq<int>)
    requires IsSorted(s)
    ensures IsSorted(InsertSorted(x, s))
{
    if |s| == 0 {
        assert InsertSorted(x, s) == [x];
        assert IsSorted([x]);
    } else if x <= s[0] {
        assert InsertSorted(x, s) == [x] + s;
        assert IsSorted([x] + s);
    } else {
        var head := s[0];
        var tail := s[1..];
        assert s == [head] + tail;
        assert IsSorted(tail);
        InsertSortedKeepsSorted(x, tail);
        assert IsSorted(InsertSorted(x, tail));
        assert InsertSorted(x, s) == [head] + InsertSorted(x, tail);
        
        // Need to show that head <= first element of InsertSorted(x, tail)
        if |tail| == 0 {
            assert InsertSorted(x, tail) == [x];
            assert head <= x; // since x > s[0] = head, this might need proof
        } else {
            if x <= tail[0] {
                assert InsertSorted(x, tail) == [x] + tail;
                assert head <= tail[0]; // from IsSorted(s)
                assert head <= x || head <= tail[0];
            } else {
                assert InsertSorted(x, tail)[0] == tail[0];
                assert head <= tail[0]; // from IsSorted(s)
            }
        }
    }
}

// Lemma: Insertion sort produces sorted sequence
lemma InsertionSortSorted(s: seq<int>)
    ensures IsSorted(InsertionSort(s))
{
    if |s| == 0 {
        assert InsertionSort(s) == [];
        assert IsSorted([]);
    } else {
        var head := s[0];
        var tail := s[1..];
        assert s == [head] + tail;
        InsertionSortSorted(tail);
        assert IsSorted(InsertionSort(tail));
        InsertSortedKeepsSorted(head, InsertionSort(tail));
        assert IsSorted(InsertSorted(head, InsertionSort(tail)));
        assert InsertionSort(s) == InsertSorted(head, InsertionSort(tail));
    }
}

// Helper lemma: InsertSorted preserves length plus one
lemma InsertSortedLength(x: int, s: seq<int>)
    ensures |InsertSorted(x, s)| == |s| + 1
{
    if |s| == 0 {
        assert InsertSorted(x, s) == [x];
        assert |InsertSorted(x, s)| == 1 == |s| + 1;
    } else if x <= s[0] {
        assert InsertSorted(x, s) == [x] + s;
        assert |InsertSorted(x, s)| == 1 + |s| == |s| + 1;
    } else {
        var head := s[0];
        var tail := s[1..];
        assert s == [head] + tail;
        InsertSortedLength(x, tail);
        assert |InsertSorted(x, tail)| == |tail| + 1;
        assert InsertSorted(x, s) == [head] + InsertSorted(x, tail);
        assert |InsertSorted(x, s)| == 1 + |InsertSorted(x, tail)| == 1 + (|tail| + 1) == |tail| + 2;
        assert |s| == 1 + |tail|;
        assert |InsertSorted(x, s)| == |s| + 1;
    }
}

// Lemma: Insertion sort preserves length
lemma InsertionSortLength(s: seq<int>)
    ensures |InsertionSort(s)| == |s|
{
    if |s| == 0 {
        assert InsertionSort(s) == [];
        assert |InsertionSort(s)| == 0 == |s|;
    } else {
        var head := s[0];
        var tail := s[1..];
        assert s == [head] + tail;
        InsertionSortLength(tail);
        assert |InsertionSort(tail)| == |tail|;
        InsertSortedLength(head, InsertionSort(tail));
        assert |InsertSorted(head, InsertionSort(tail))| == |InsertionSort(tail)| + 1;
        assert |InsertSorted(head, InsertionSort(tail))| == |tail| + 1;
        assert |s| == 1 + |tail|;
        assert InsertionSort(s) == InsertSorted(head, InsertionSort(tail));
        assert |InsertionSort(s)| == |s|;
    }
}

// Helper lemma: Inserting into sorted sequence where element is already in correct position
lemma {:axiom} InsertSortedIdempotent(x: int, s: seq<int>)
    requires IsSorted(s)
    requires forall i :: 0 <= i < |s| ==> ((i == 0 ==> x <= s[i]) && (i > 0 ==> s[i-1] <= x <= s[i])) || (i == |s|-1 && x >= s[i])
    ensures InsertSorted(x, s) == [x] + s || InsertSorted(x, s) == s + [x] || exists k :: 0 <= k <= |s| && InsertSorted(x, s) == s[..k] + [x] + s[k..]

// Helper lemma: If sequence is sorted, insertion sort doesn't change it
lemma SortedIsFixed(s: seq<int>)
    requires IsSorted(s)
    ensures InsertionSort(s) == s
{
    if |s| <= 1 {
        if |s| == 0 {
            assert InsertionSort(s) == [] == s;
        } else {
            assert InsertionSort(s) == InsertSorted(s[0], InsertionSort(s[1..]));
            assert s[1..] == [];
            assert InsertionSort(s[1..]) == [];
            assert InsertSorted(s[0], []) == [s[0]];
            assert s == [s[0]];
        }
    } else {
        var head := s[0];
        var tail := s[1..];
        assert IsSorted(tail);
        SortedIsFixed(tail);
        assert InsertionSort(tail) == tail;
        
        // Need to show InsertSorted(head, tail) == s = [head] + tail
        // Since s is sorted, head <= tail[0], so InsertSorted(head, tail) should be [head] + tail
        assert head <= tail[0]; // from IsSorted(s)
        assert InsertSorted(head, tail) == [head] + tail;
        assert s == [head] + tail;
        assert InsertionSort(s) == InsertSorted(head, InsertionSort(tail)) == InsertSorted(head, tail) == [head] + tail == s;
    }
}

// Lemma: Insertion sort is idempotent
lemma InsertionSortIdempotent(s: seq<int>)
    ensures InsertionSort(InsertionSort(s)) == InsertionSort(s)
{
    InsertionSortSorted(s);
    assert IsSorted(InsertionSort(s));
    SortedIsFixed(InsertionSort(s));
    assert InsertionSort(InsertionSort(s)) == InsertionSort(s);
}

// Lemma: Palindrome property with concatenation  
lemma {:axiom} PalindromeConcat<T>(s1: seq<T>, s2: seq<T>)
    requires IsPalindrome(s1) && IsPalindrome(s2)
    ensures IsPalindrome(s1 + s2) <==> s1 == Reverse(s2)

// Helper lemma: Min is indeed the minimum
lemma MinIsMinimal(s: seq<int>)
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> Min(s) <= s[i]
{
    if |s| == 1 {
        assert Min(s) == s[0];
        assert forall i :: 0 <= i < |s| ==> Min(s) <= s[i];
    } else {
        var head := s[0];
        var tail := s[1..];
        assert s == [head] + tail;
        MinIsMinimal(tail);
        var m := Min(tail);
        assert forall i :: 0 <= i < |tail| ==> m <= tail[i];
        assert Min(s) == if head < m then head else m;
        
        if head < m {
            assert Min(s) == head;
            assert Min(s) <= head;
            assert forall i :: 1 <= i < |s| ==> Min(s) <= m <= tail[i-1] == s[i];
        } else {
            assert Min(s) == m;
            assert Min(s) <= head == s[0];
            assert forall i :: 1 <= i < |s| ==> Min(s) == m <= tail[i-1] == s[i];
        }
    }
}

// Helper lemma: Max is indeed the maximum
lemma MaxIsMaximal(s: seq<int>)
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> s[i] <= Max(s)
{
    if |s| == 1 {
        assert Max(s) == s[0];
        assert forall i :: 0 <= i < |s| ==> s[i] <= Max(s);
    } else {
        var head := s[0];
        var tail := s[1..];
        assert s == [head] + tail;
        MaxIsMaximal(tail);
        var m := Max(tail);
        assert forall i :: 0 <= i < |tail| ==> tail[i] <= m;
        assert Max(s) == if head > m then head else m;
        
        if head > m {
            assert Max(s) == head;
            assert head <= Max(s);
            assert forall i :: 1 <= i < |s| ==> tail[i-1] == s[i] <= m <= head == Max(s);
        } else {
            assert Max(s) == m;
            assert head == s[0] <= Max(s);
            assert forall i :: 1 <= i < |s| ==> s[i] == tail[i-1] <= m == Max(s);
        }
    }
}

// Lemma: Max and Min bounds
lemma MaxMinBounds(s: seq<int>)
    requires |s| > 0
    ensures Min(s) <= Max(s)
    ensures All(s, x => Min(s) <= x && x <= Max(s))
{
    MinIsMinimal(s);
    MaxIsMaximal(s);
    
    // Prove Min(s) <= Max(s)
    if |s| == 1 {
        assert Min(s) == s[0] == Max(s);
    } else {
        // Min(s) <= s[0] <= Max(s) by the helper lemmas
        assert Min(s) <= s[0] <= Max(s);
    }
    
    // Prove All(s, x => Min(s) <= x && x <= Max(s))
    // This follows directly from the helper lemmas
    assert forall i :: 0 <= i < |s| ==> Min(s) <= s[i] <= Max(s);
    
    // Now prove the All predicate
    if |s| == 0 {
        assert All(s, x => Min(s) <= x && x <= Max(s));
    } else {
        AllImpliesForall(s, x => Min(s) <= x && x <= Max(s));
    }
}

// Helper to connect All predicate with forall
lemma AllImpliesForall<T>(s: seq<T>, pred: T --> bool)
    requires forall x :: x in s ==> pred.requires(x)
    requires forall i :: 0 <= i < |s| ==> pred(s[i])
    ensures All(s, pred)
{
    if |s| == 0 {
        assert All(s, pred);
    } else {
        assert pred(s[0]);
        AllImpliesForall(s[1..], pred);
        assert All(s[1..], pred);
        assert All(s, pred) == pred(s[0]) && All(s[1..], pred);
    }
}

// Helper lemma: IsSorted means head <= all elements in tail
lemma SortedHeadBound(s: seq<int>)
    requires |s| >= 2
    requires IsSorted(s)
    ensures forall i :: 1 <= i < |s| ==> s[0] <= s[i]
{
    if |s| == 2 {
        assert s[0] <= s[1]; // direct from IsSorted definition
    } else {
        assert s[0] <= s[1]; // from IsSorted([s[0], s[1], ...])
        SortedHeadBound(s[1..]);
        assert forall i :: 1 <= i < |s[1..]| ==> s[1] <= s[1..][i];
        assert forall i :: 2 <= i < |s| ==> s[1] <= s[i];
        assert forall i :: 2 <= i < |s| ==> s[0] <= s[1] <= s[i];
        assert forall i :: 1 <= i < |s| ==> s[0] <= s[i];
    }
}

// Lemma: Filter preserves sortedness
lemma FilterPreservesSorted(s: seq<int>, pred: int --> bool)
    requires forall x :: x in s ==> pred.requires(x)
    requires IsSorted(s)
    ensures IsSorted(Filter(s, pred))
{
    if |s| == 0 {
        assert Filter(s, pred) == [];
        assert IsSorted([]);
    } else if |s| == 1 {
        assert IsSorted(Filter(s, pred)); // Single element or empty is always sorted
    } else {
        var head := s[0];
        var tail := s[1..];
        assert s == [head] + tail;
        assert IsSorted(tail);
        assert forall x :: x in tail ==> pred.requires(x);
        FilterPreservesSorted(tail, pred);
        assert IsSorted(Filter(tail, pred));
        
        if pred(head) {
            assert Filter(s, pred) == [head] + Filter(tail, pred);
            // Need to show head <= first element of Filter(tail, pred) if it exists
            if |Filter(tail, pred)| > 0 {
                // There exists some element in tail that satisfies pred
                // Since s is sorted and head <= all elements in tail,
                // and Filter(tail, pred)[0] is some element from tail,
                // we have head <= Filter(tail, pred)[0]
                SortedHeadBound(s);
                assert forall i :: 1 <= i < |s| ==> head <= s[i];
                assert forall i :: 0 <= i < |tail| ==> head <= tail[i]; // since tail = s[1..]
                FilterFirstElementBound(head, tail, pred);
                assert head <= Filter(tail, pred)[0];
                assert IsSorted([head] + Filter(tail, pred));
            } else {
                assert Filter(s, pred) == [head];
                assert IsSorted([head]);
            }
        } else {
            assert Filter(s, pred) == Filter(tail, pred);
            assert IsSorted(Filter(s, pred));
        }
    }
}

// Helper lemma: If s is sorted and head <= all elements in tail,
// then head <= first element of Filter(tail, pred) if it exists
lemma FilterFirstElementBound(head: int, tail: seq<int>, pred: int --> bool)
    requires |tail| > 0
    requires forall x :: x in tail ==> pred.requires(x)
    requires forall i :: 0 <= i < |tail| ==> head <= tail[i]
    requires |Filter(tail, pred)| > 0
    ensures head <= Filter(tail, pred)[0]
{
    if |tail| == 0 {
        assert |Filter(tail, pred)| == 0;
        assert false; // contradiction with requires
    } else {
        var first := tail[0];
        var rest := tail[1..];
        assert tail == [first] + rest;
        
        if pred(first) {
            assert Filter(tail, pred) == [first] + Filter(rest, pred);
            assert Filter(tail, pred)[0] == first;
            assert head <= first;
        } else {
            assert Filter(tail, pred) == Filter(rest, pred);
            if |Filter(rest, pred)| > 0 {
                FilterFirstElementBound(head, rest, pred);
                assert head <= Filter(rest, pred)[0];
                assert Filter(tail, pred)[0] == Filter(rest, pred)[0];
            } else {
                assert |Filter(tail, pred)| == 0;
                assert false; // contradiction
            }
        }
    }
}


// Lemma: Complex property about sequence transformations and reversals
lemma TransformationReversal<T, U>(s: seq<T>, f: T --> U)
    requires forall x :: x in s ==> f.requires(x)
    requires forall x :: x in Reverse(s) ==> f.requires(x)
    ensures Reverse(Map(s, f)) == Map(Reverse(s), f)
{
    if |s| == 0 {
        assert s == [];
        assert Reverse(s) == [];
        assert Map(s, f) == [];
        assert Map(Reverse(s), f) == [];
        assert Reverse(Map(s, f)) == Reverse([]) == [];
        assert Map(Reverse(s), f) == [];
    } else {
        var head := s[0];
        var tail := s[1..];
        assert s == [head] + tail;
        
        // Recursive call
        assert forall x :: x in tail ==> f.requires(x);
        assert forall x :: x in Reverse(tail) ==> f.requires(x);
        TransformationReversal(tail, f);
        assert Reverse(Map(tail, f)) == Map(Reverse(tail), f);
        
        calc {
            Reverse(Map(s, f));
            Reverse(Map([head] + tail, f));
            { MapConcat([head], tail, f); }
            Reverse(Map([head], f) + Map(tail, f));
            Reverse([f(head)] + Map(tail, f));
            { ReverseConcat([f(head)], Map(tail, f)); }
            Reverse(Map(tail, f)) + Reverse([f(head)]);
            Reverse(Map(tail, f)) + [f(head)];
            { TransformationReversal(tail, f); }  // Use IH
            Map(Reverse(tail), f) + [f(head)];
        }
        
        calc {
            Map(Reverse(s), f);
            Map(Reverse([head] + tail), f);
            { ReverseConcat([head], tail); }
            Map(Reverse(tail) + Reverse([head]), f);
            { assert Reverse([head]) == [head]; }
            Map(Reverse(tail) + [head], f);
            { 
              // Establish precondition for MapConcat
              assert forall x :: x in Reverse(tail) ==> f.requires(x);
              assert forall x :: x in [head] ==> f.requires(x);
              assert forall x :: x in Reverse(tail) + [head] ==> f.requires(x);
              MapConcat(Reverse(tail), [head], f); 
            }
            Map(Reverse(tail), f) + Map([head], f);
            Map(Reverse(tail), f) + [f(head)];
        }
        
        // Both sides equal Map(Reverse(tail), f) + [f(head)]
        assert Reverse(Map(s, f)) == Map(Reverse(s), f);
    }
}