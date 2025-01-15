// union-find
//https://dafny.org/latest/Dafny-cheat-sheet.pdf
//https://dafny.org/latest/DafnyCheatsheet.pdf

    datatype MultimiDisjuncte = MultimiDisjuncte(parinte: seq<int>, rang: seq<int>)

    function Initial(n: int): MultimiDisjuncte
        requires n > 0
        ensures |MultimiDisjuncte(seq(n, i => i), seq(n, i => 0)).parinte| == n
        ensures |MultimiDisjuncte(seq(n, i => i), seq(n, i => 0)).rang| == n
        ensures forall i :: 0 <= i < n ==> 
            MultimiDisjuncte(seq(n, i => i), seq(n, i => 0)).parinte[i] == i &&
            MultimiDisjuncte(seq(n, i => i), seq(n, i => 0)).rang[i] == 0
        ensures validMultimi(Initial(n))
    {
        MultimiDisjuncte(
            parinte := seq(n, i => i), 
            rang := seq(n, i => 0)
        )
    }
predicate validMultimi(md: MultimiDisjuncte){
    |md.parinte| == |md.rang| && forall x  :: 0 <= x < |md.parinte| ==> 0 <= md.parinte[x] < |md.parinte|
}

// Method to find the leader of a set (with path compression)
    method Cautare(md: MultimiDisjuncte, x: int) returns (lider: int, updated: MultimiDisjuncte)
        requires 0 <= x < |md.parinte|
        requires validMultimi(md)
        ensures 0 <= lider < |md.parinte|
        ensures 0 <= lider < |updated.parinte|
        ensures updated.parinte[lider] == lider
        ensures validMultimi(updated)
        ensures |md.parinte| == |updated.parinte|
        decreases *
        //ensures forall i :: 0 <= i < |md.parinte| && old(md.parinte[i]) == i ==> updated.parinte[i] == lider
    {
        if md.parinte[x] == x
        {
            assert 0 <= md.parinte[x] < |md.parinte|;
            return x, md; 
        }
        else
        {
            assert 0 <= md.parinte[x] < |md.parinte|;
            var root, newState := Cautare(md, md.parinte[x]);        
            var newState' :=  MultimiDisjuncte (newState.parinte, newState.rang);
            return root, MultimiDisjuncte(newState.parinte, newState.rang); 
        }
    }  

method Unire(md: MultimiDisjuncte, x: int, y: int) returns (updated: MultimiDisjuncte)
    requires 0 <= x < |md.parinte|
    requires 0 <= y < |md.parinte|
    requires validMultimi(md)
    // modifies md // metoda modifica md
    ensures validMultimi(updated)  
    requires 0 <= x < |md.parinte|
    requires 0 <= y < |md.parinte|
    // ensures updated.parinte[x] == updated.parinte[y] 
    // ensures forall i :: 0 <= i < |md.parinte| ==> 
    //     (exists lider :: 0 <= lider < |md.parinte| && updated.parinte[i] == lider)
    decreases *
{
    var liderX, state1 := Cautare(md, x);
    var liderY, state2 := Cautare(state1, y);

    if liderX != liderY {
        if state2.rang[liderX] < state2.rang[liderY] {
            updated:= MultimiDisjuncte(state2.parinte[liderX := liderY], state2.rang);
        } else if state2.rang[liderX] > state2.rang[liderY] {
            updated:= MultimiDisjuncte(state2.parinte[liderY := liderX], state2.rang); 
        } else {
            updated:= MultimiDisjuncte(state2.parinte[liderY := liderX], state2.rang);
            updated:= MultimiDisjuncte(state2.rang[liderX := liderX], state2.parinte);
        }
    }
    updated := state2;
}