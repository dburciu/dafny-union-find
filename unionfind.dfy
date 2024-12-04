// Easy-Medium Projects: implement, specify, and verify an algorithm or data structure
// Estimated Complexity: Easy-Medium

// Suggested team size: 1-2

// union-find


class MultimiDisjuncte 
{
    var parinte: array<int>;
    var rang: array <int>;

    constructor(n: int)
        requires n > 0
        ensures parinte.Length == n && rang.Length == n
        ensures forall i :: 0 <= i < n ==> parinte[i] == i && rang[i] == 0
        
    {
        var parinte': array<int> := new int[n];
        var rang': array<int> := new int[n];

        parinte := new int[n];
        rang := new int[n];
        new;
        for i := 0 to n {
            parinte'[i] := i;
            rang'[i] := 0;
        }
        parinte := parinte';
        rang := rang';
    }
}

method Cautare(x: int)
    requires 0 <= x < parinte.Length
    ensures 0 <= lider < parinte.Length
    ensures parinte[lider] == lider
    ensures forall i :: 0 <= i < parinte.Length && old(parinte[i]) == i ==> parinte[i] == lider
    {
        if parinte'[x] != x {
        parinte'[x] := Gaseste(parinte'[x]);
        }
        return parinte'[x];
    }

// method Uneste(x:int, y:int)
