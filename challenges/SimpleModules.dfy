// Module for basic arithmetic operations and properties
module ArithmeticProperties {
    
    // Function to compute factorial
    function factorial(n: nat): nat
        decreases n
    {
        if n == 0 then 1 else n * factorial(n - 1)
    }
    
    // Function to compute Fibonacci numbers
    function fib(n: nat): nat
        decreases n
    {
        if n <= 1 then n else fib(n - 1) + fib(n - 2)
    }
    
    // Lemma: Fibonacci growth property
    lemma FibGrowth(n: nat)
        requires n >= 2
        ensures fib(n) >= n
        decreases n
    { }
}

// Module for list operations and properties
module ListOperations {
    
    // Function to compute the sum of a list
    function sum(lst: seq<int>): int
    {
        if |lst| == 0 then 0 else lst[0] + sum(lst[1..])
    }
    
    // Function to reverse a list
    function reverse<T>(lst: seq<T>): seq<T>
    {
        if |lst| == 0 then [] else reverse(lst[1..]) + [lst[0]]
    }
    
    // Function to append two lists
    function append<T>(lst1: seq<T>, lst2: seq<T>): seq<T>
    {
        lst1 + lst2
    }
    
    // Lemma: Sum is distributive over concatenation
    lemma SumDistributive(lst1: seq<int>, lst2: seq<int>)
        ensures sum(append(lst1, lst2)) == sum(lst1) + sum(lst2)
    { }
    
    // Lemma: Reverse is involutive (reversing twice gives original)
    lemma ReverseInvolutive<T>(lst: seq<T>)
        ensures reverse(reverse(lst)) == lst
        decreases |lst|
    { }
}

// Module that combines lists and Fibonacci properties
module FibonacciLists {
    import A = ArithmeticProperties
    import L = ListOperations
    
    // Function to generate a list of the first n Fibonacci numbers
    function fibList(n: nat): seq<nat>
        decreases n
    {
        if n == 0 then []
        else fibList(n - 1) + [A.fib(n - 1)]
    }
    
    // Function to compute sum of first n Fibonacci numbers
    function fibSum(n: nat): nat
        decreases n
    {
        if n == 0 then 0 else A.fib(n - 1) + fibSum(n - 1)
    }
    
    // Lemma: The sum of a Fibonacci list equals the direct Fibonacci sum
    lemma FibListSumEquivalence(n: nat)
        ensures L.sum(fibList(n)) == fibSum(n)
        decreases n
    { }
    
    // Lemma: Reversing a Fibonacci list preserves the sum
    lemma FibListReverseSum(n: nat)
        ensures L.sum(L.reverse(fibList(n))) == L.sum(fibList(n))
        decreases n
    { }

}