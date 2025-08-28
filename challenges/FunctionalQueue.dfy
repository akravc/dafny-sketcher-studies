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
}

lemma ReverseOfReverse<T>(s: seq<T>)
    ensures Reverse(Reverse(s)) == s
{
}

lemma SeqAssociativity<T>(s1: seq<T>, s2: seq<T>, s3: seq<T>)
    ensures (s1 + s2) + s3 == s1 + (s2 + s3)
{
}

lemma ReverseDistributesOverConcat<T>(s1: seq<T>, s2: seq<T>)
    ensures Reverse(s1 + s2) == Reverse(s2) + Reverse(s1)
{
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
}

lemma DequeueCorrectness<T>(q: Queue<T>)
    requires !IsEmpty(q)
    ensures var (newQ, x) := Dequeue(q); 
            Size(newQ) == Size(q) - 1 &&
            ToSeq(q) == [x] + ToSeq(newQ)
{
}

lemma NormalizePreservesToSeq<T>(q: Queue<T>)
    ensures ToSeq(Normalize(q)) == ToSeq(q)
{
}

lemma NormalizePreservesSize<T>(q: Queue<T>)
    ensures Size(Normalize(q)) == Size(q)
{
}

lemma PeekCorrectness<T>(q: Queue<T>)
    requires !IsEmpty(q)
    ensures var x := Peek(q);
            var s := ToSeq(q);
            |s| > 0 && x == s[0]
{
}

lemma QueueInvariant<T>(q: Queue<T>)
    ensures IsEmpty(q) <==> (Size(q) == 0)
    ensures IsEmpty(q) <==> (|ToSeq(q)| == 0)
    ensures Size(q) == |ToSeq(q)|
{
}