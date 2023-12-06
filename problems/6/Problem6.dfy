include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
include "../../libraries/src/dafny/Collections/Seqs.dfy"
include "../../libraries/src/Wrappers.dfy"
module Problem6 {
    import opened Split
    import opened ParseInt
    import opened Dafny.Collections.Seq
    import opened Wrappers
    function abs(x: int): nat {
        if x < 0 then -x else x
    }

    method parseInput(input: string) returns (time: seq<nat>, distance: seq<nat>) 
    {
        var lines := Filter(x => x != "", splitOnBreak(input));
        assume {:axiom} |lines| == 2;
        time := Map(x => abs(Integer(x)), Filter(piece => |piece| > 0 && charInNC(piece[0]) , split(lines[0], " ")));
        distance := Map(x => abs(Integer(x)), Filter(piece => |piece| > 0 && charInNC(piece[0]) , split(lines[1], " ")));
    }

    method parseInput2(input: string) returns (time: seq<nat>, distance: seq<nat>) 
    {
        var lines := Filter(x => x != "", splitOnBreak(input));
        assume {:axiom} |lines| == 2;
        var what: string := FoldLeft((x,y) => (x+y),"",Filter((piece: string) => |piece| > 0 && charInNC(piece[0]) , split(lines[0], " ")));
        time := [abs(Integer(what))];
        distance := [abs(Integer(FoldLeft((x,y) => x+y,"", Filter(piece => |piece| > 0 && charInNC(piece[0]) , split(lines[1], " ")))))];
    }
    method problem6_1(input: string) returns (x: int) {
        var times, distance := parseInput(input);
        print times, "\n";
        print distance, "\n";
        if |times| == |distance| {
            var wins: seq<nat> := [];
            for i :=0 to |times| {
                var raceDistances: seq<int> := [];
                for k := 0 to times[i] {
                    raceDistances := raceDistances + [k*(times[i]-k)];
                }
                print raceDistances, "\n";
                var count := |Filter(x => x > distance[i], raceDistances)|;
                wins := wins + [count];
            }
            return FoldLeft((x,y) => x * y, 1, wins);
        }
        return 3;
    }

    method problem6_2(input: string) returns (x: int) {
        var times, distance := parseInput2(input);
        print times, "\n";
        print distance, "\n";
        if |times| == |distance| {
            var wins: nat := 0;
            for i :=0 to |times| {
                for k := 0 to times[i] {
                    var raceDistance := k*(times[i]-k);
                    if raceDistance > distance[i] {
                        wins := wins+1;
                    }
                }
            }
            return wins;
        }
        return 3;
    }
}
