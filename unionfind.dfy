// Easy-Medium Projects: implement, specify, and verify an algorithm or data structure
// Estimated Complexity: Easy-Medium

// Suggested team size: 1-2

// union-find
//Funcția trebuie să folosească o expresie returnată explicit în loc să se bazeze pe result. Contractele ensures pot fi scrise fără result, folosind direct expresia care va fi returnată.
    datatype MultimiDisjuncte = MultimiDisjuncte(parinte: seq<int>, rang: seq<int>)

    function Initial(n: int): MultimiDisjuncte
        requires n > 0
        ensures |MultimiDisjuncte(seq(n, i => i), seq(n, i => 0)).parinte| == n
        ensures |MultimiDisjuncte(seq(n, i => i), seq(n, i => 0)).rang| == n
        ensures forall i :: 0 <= i < n ==> 
            MultimiDisjuncte(seq(n, i => i), seq(n, i => 0)).parinte[i] == i &&
            MultimiDisjuncte(seq(n, i => i), seq(n, i => 0)).rang[i] == 0
    {
        MultimiDisjuncte(
            parinte := seq(n, i => i), // Secvență de la 0 la n-1
            rang := seq(n, i => 0)     // Secvență constantă de zerouri
        )
    }


// Method to find the leader of a set (with path compression)
    method Cautare(md: MultimiDisjuncte, x: int) returns (lider: int, updated: MultimiDisjuncte)
        requires 0 <= x < |md.parinte|
        ensures 0 <= lider < |md.parinte|
        ensures updated.parinte[lider] == lider
        ensures forall i :: 0 <= i < |md.parinte| && old(md.parinte[i]) == i ==> updated.parinte[i] == lider
    {
        if md.parinte[x] == x
        {
            return x, md;  // Dacă x este deja liderul, returnează x și starea originală
        }
        else
        {
            var root, newState := Cautare(md, md.parinte[x]);    // Apel recursiv pentru a găsi liderul
            // newState.parinte[x] := root;     // Actualizează părintele lui x pentru a indica spre root
            newState.parinte := newState.parinte[..x] + [root] + newState.parinte[x+1..];
            return root, MultimiDisjuncte(newState.parinte, newState.rang); // Returnează liderul și noua stare
        }
    }


//     // Method to unite two sets
//     method Uneste(x: int, y: int) returns (updated: MultimiDisjuncte)
//         requires 0 <= x < |parinte| && 0 <= y < |parinte|
//         ensures |updated.parinte| == |parinte|
//         ensures |updated.rang| == |rang|
//     {
//         var (rootX, stateAfterX) := this.Cautare(x);
//         var (rootY, stateAfterY) := stateAfterX.Cautare(y);

//         if rootX == rootY {
//             return stateAfterY;
//         }

//         if rang[rootX] < rang[rootY] {
//             var newParinte := stateAfterY.parinte[..rootX] + [rootY] + stateAfterY.parinte[rootX+1..];
//             return MultimiDisjuncte(newParinte, stateAfterY.rang);
//         } else if rang[rootX] > rang[rootY] {
//             var newParinte := stateAfterY.parinte[..rootY] + [rootX] + stateAfterY.parinte[rootY+1..];
//             return MultimiDisjuncte(newParinte, stateAfterY.rang);
//         } else {
//             var newParinte := stateAfterY.parinte[..rootY] + [rootX] + stateAfterY.parinte[rootY+1..];
//             var newRang := stateAfterY.rang[..rootX] + [rang[rootX] + 1] + stateAfterY.rang[rootX+1..];
//             return MultimiDisjuncte(newParinte, newRang);
//         }
//     }
// }

// method Main()
// {
//     var d := MultimiDisjuncte.Initial(5); // Initialize a disjoint set with 5 elements
//     d := d.Uneste(0, 1);                  // Union sets containing 0 and 1
//     d := d.Uneste(3, 4);                  // Union sets containing 3 and 4
//     var (leader, d) := d.Cautare(1);      // Find the leader of the set containing 1
//     assert leader == 0;                   // Verify the leader