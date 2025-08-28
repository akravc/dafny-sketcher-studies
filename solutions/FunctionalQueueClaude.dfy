datatype Queue<T> = Queue(front: seq<T>, back: seq<T>)

function IsEmpty<T>(q: Queue<T>): bool
{
    |q.front| == 0 && |q.back| == 0
}

function Size<T>(q: Queue<T>): nat
{
    |q.front| + |q.back|
}

function ToSeq<T>(q: Queue<T>): seq<T>
{
    q.front + Reverse(q.back)
}

function Reverse<T>(s: seq<T>): seq<T>
{
    if |s| == 0 then []
    else Reverse(s[1..]) + [s[0]]
}

function Empty<T>(): Queue<T>
{
    Queue([], [])
}

function Normalize<T>(q: Queue<T>): Queue<T>
{
    if |q.front| == 0 && |q.back| > 0 then
        Queue(Reverse(q.back), [])
    else
        q
}

function Enqueue<T>(q: Queue<T>, x: T): Queue<T>
{
    Queue(q.front, [x] + q.back)
}

function Dequeue<T>(q: Queue<T>): (Queue<T>, T)
    requires !IsEmpty(q)
{
    var normalized := Normalize(q);
    (Queue(normalized.front[1..], normalized.back), normalized.front[0])
}

function Peek<T>(q: Queue<T>): T
    requires !IsEmpty(q)
{
    var normalized := Normalize(q);
    normalized.front[0]
}

lemma ReversePreservesLength<T>(s: seq<T>)
    ensures |Reverse(s)| == |s|
{
    if |s| == 0 {
    } else {
        ReversePreservesLength(s[1..]);
    }
}

lemma ReverseOfReverse<T>(s: seq<T>)
    ensures Reverse(Reverse(s)) == s
{
    if |s| == 0 {
        assert Reverse<T>([]) == [];
        assert Reverse<T>(Reverse<T>([])) == Reverse<T>([]) == [];
    } else {
        ReverseOfReverse(s[1..]);
        calc {
            Reverse(Reverse(s));
            { assert s == [s[0]] + s[1..]; }
            Reverse(Reverse([s[0]] + s[1..]));
            { ReverseDistributesOverConcat([s[0]], s[1..]); }
            Reverse(Reverse(s[1..]) + Reverse([s[0]]));
            { assert Reverse([s[0]]) == [s[0]]; }
            Reverse(Reverse(s[1..]) + [s[0]]);
            { ReverseDistributesOverConcat(Reverse(s[1..]), [s[0]]); }
            Reverse([s[0]]) + Reverse(Reverse(s[1..]));
            { assert Reverse([s[0]]) == [s[0]]; }
            [s[0]] + Reverse(Reverse(s[1..]));
            { assert Reverse(Reverse(s[1..])) == s[1..]; }
            [s[0]] + s[1..];
            s;
        }
    }
}

lemma SeqAssociativity<T>(s1: seq<T>, s2: seq<T>, s3: seq<T>)
    ensures (s1 + s2) + s3 == s1 + (s2 + s3)
{
}

lemma ReverseDistributesOverConcat<T>(s1: seq<T>, s2: seq<T>)
    ensures Reverse(s1 + s2) == Reverse(s2) + Reverse(s1)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
        assert Reverse(s1) == [];
        assert Reverse(s2) + Reverse(s1) == Reverse(s2) + [];
        assert Reverse(s2) + [] == Reverse(s2);
    } else {
        ReverseDistributesOverConcat(s1[1..], s2);
        calc {
            Reverse(s1 + s2);
            { assert s1 == [s1[0]] + s1[1..]; }
            Reverse([s1[0]] + s1[1..] + s2);
            { SeqAssociativity([s1[0]], s1[1..], s2); }
            Reverse([s1[0]] + (s1[1..] + s2));
            Reverse(s1[1..] + s2) + [s1[0]];
            { assert Reverse(s1[1..] + s2) == Reverse(s2) + Reverse(s1[1..]); }
            (Reverse(s2) + Reverse(s1[1..])) + [s1[0]];
            { SeqAssociativity(Reverse(s2), Reverse(s1[1..]), [s1[0]]); }
            Reverse(s2) + (Reverse(s1[1..]) + [s1[0]]);
            Reverse(s2) + Reverse(s1);
        }
    }
}

lemma EmptyQueueCorrectness<T>()
    ensures IsEmpty(Empty<T>())
    ensures Size(Empty<T>()) == 0
    ensures ToSeq(Empty<T>()) == []
{
}

lemma EnqueueCorrectness<T>(q: Queue<T>, x: T)
    ensures !IsEmpty(Enqueue(q, x))
    ensures Size(Enqueue(q, x)) == Size(q) + 1
    ensures ToSeq(Enqueue(q, x)) == ToSeq(q) + [x]
{
    var newQ := Enqueue(q, x);
    assert newQ.front == q.front;
    assert newQ.back == [x] + q.back;
    
    calc {
        ToSeq(newQ);
        newQ.front + Reverse(newQ.back);
        q.front + Reverse([x] + q.back);
        { ReverseDistributesOverConcat([x], q.back); }
        q.front + (Reverse(q.back) + Reverse([x]));
        q.front + (Reverse(q.back) + [x]);
        (q.front + Reverse(q.back)) + [x];
        ToSeq(q) + [x];
    }
}

lemma DequeueCorrectness<T>(q: Queue<T>)
    requires !IsEmpty(q)
    ensures var (newQ, x) := Dequeue(q); 
            Size(newQ) == Size(q) - 1 &&
            ToSeq(q) == [x] + ToSeq(newQ)
{
    var (newQ, x) := Dequeue(q);
    var normalized := Normalize(q);
    
    assert newQ == Queue(normalized.front[1..], normalized.back);
    assert x == normalized.front[0];
    
    NormalizePreservesToSeq(q);
    assert ToSeq(normalized) == ToSeq(q);
    
    if |q.front| > 0 {
        assert normalized == q;
        assert ToSeq(q) == q.front + Reverse(q.back);
        assert ToSeq(newQ) == q.front[1..] + Reverse(q.back);
        assert q.front == [q.front[0]] + q.front[1..];
        assert ToSeq(q) == [q.front[0]] + q.front[1..] + Reverse(q.back);
        assert ToSeq(q) == [x] + ToSeq(newQ);
    } else {
        assert |q.front| == 0 && |q.back| > 0;
        assert normalized.front == Reverse(q.back);
        assert normalized.back == [];
        ReversePreservesLength(q.back);
        assert |normalized.front| > 0;
        assert x == normalized.front[0];
        assert ToSeq(newQ) == normalized.front[1..] + Reverse([]);
        assert ToSeq(newQ) == normalized.front[1..];
        assert normalized.front == [normalized.front[0]] + normalized.front[1..];
        assert ToSeq(normalized) == normalized.front;
        assert ToSeq(q) == [x] + ToSeq(newQ);
    }
}

lemma NormalizePreservesToSeq<T>(q: Queue<T>)
    ensures ToSeq(Normalize(q)) == ToSeq(q)
{
    if |q.front| == 0 && |q.back| > 0 {
        var normalized := Normalize(q);
        calc {
            ToSeq(normalized);
            normalized.front + Reverse(normalized.back);
            Reverse(q.back) + Reverse([]);
            Reverse(q.back) + [];
            Reverse(q.back);
            [] + Reverse(q.back);
            q.front + Reverse(q.back);
            ToSeq(q);
        }
    } else {
        assert Normalize(q) == q;
    }
}

lemma NormalizePreservesSize<T>(q: Queue<T>)
    ensures Size(Normalize(q)) == Size(q)
{
    if |q.front| == 0 && |q.back| > 0 {
        ReversePreservesLength(q.back);
    }
}

lemma PeekCorrectness<T>(q: Queue<T>)
    requires !IsEmpty(q)
    ensures var x := Peek(q);
            var s := ToSeq(q);
            |s| > 0 && x == s[0]
{
    var x := Peek(q);
    var normalized := Normalize(q);
    
    NormalizePreservesToSeq(q);
    assert ToSeq(normalized) == ToSeq(q);
    
    if |q.front| > 0 {
        assert normalized == q;
        assert x == q.front[0];
        var s := ToSeq(q);
        assert s == q.front + Reverse(q.back);
        assert |q.front| > 0;
        assert s[0] == q.front[0];
        assert x == s[0];
    } else {
        assert |q.front| == 0 && |q.back| > 0;
        assert normalized.front == Reverse(q.back);
        ReversePreservesLength(q.back);
        assert |normalized.front| > 0;
        assert x == normalized.front[0];
        var s := ToSeq(q);
        assert s == [] + Reverse(q.back);
        assert s == Reverse(q.back);
        assert s == normalized.front;
        assert x == s[0];
    }
}

lemma QueueInvariant<T>(q: Queue<T>)
    ensures IsEmpty(q) <==> (Size(q) == 0)
    ensures IsEmpty(q) <==> (|ToSeq(q)| == 0)
    ensures Size(q) == |ToSeq(q)|
{
    ReversePreservesLength(q.back);
}
