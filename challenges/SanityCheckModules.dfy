module NatModule {
    datatype Nat = Z | S(n: Nat)
    function add(n1: Nat, n2: Nat): Nat
    {
        match n1
        case Z => n2
        case S(n) => S(add(n, n2))
    }

    lemma add_comm(n1: Nat, n2: Nat)
    ensures add(n1, n2) == add(n2, n1)
    {
    }
}

module ListModule {
    datatype List<T> = Nil | Cons(h: T, t: List<T>)
    function remove<T(==)>(xs: List<T>, x: T): List<T>
    {
        match xs
        case Nil => Nil
        case Cons(h, t) => if h==x then remove(t, x) else Cons(h, remove(t, x))
    }
}

module NatListModule {
    import NM = NatModule
    import LM = ListModule

    function sum(xs: LM.List<NM.Nat>): NM.Nat
    {
        match xs
        case Nil => NM.Z
        case Cons(h, t) => NM.add(h, sum(t))
    }

    lemma sum0(xs: LM.List<NM.Nat>)
    ensures sum(xs) == sum(LM.Cons(NM.Z, xs))
    {
    }

    lemma sum_remove0(xs: LM.List<NM.Nat>)
    ensures sum(xs) == sum(LM.remove(xs, NM.Z))
    {
    }
}