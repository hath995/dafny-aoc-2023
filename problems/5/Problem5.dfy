include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
include "../../libraries/src/dafny/Collections/Seqs.dfy"
include "../../libraries/src/Wrappers.dfy"
module Problem5 {
    import opened Split
    import opened ParseInt
    import opened Dafny.Collections.Seq
    import opened Wrappers
    function abs(x: int): nat {
        if x < 0 then -x else x
    }
    function min(a: nat ,b:nat): nat {
        if a < b then a else b
    }

    function rangeMapper(range: seq<seq<nat>>): nat -> nat 
        requires forall x:: x in range ==> |x| == 3 
        ensures forall x:nat :: rangeMapper(range).requires(x)
    {
        (x: nat) => if |range| == 0 then 
            x 
        else if range[0][1] <= x < range[0][1]+range[0][2] then 
            range[0][0]+(x-range[0][1])
        else 
            rangeMapper(range[1..])(x)
    }
    // function rangeMapper(range: seq<seq<nat>>): nat -> nat {
    //     (z: nat) => z
    // }

    method parseInput(input:string) returns (seeds: seq<nat>, maps: seq<nat -> nat>) {
        maps :=[];
        seeds := [];
        var sectionStrings := splitOnDoubleBreak(input);
        assume {:axiom} |sectionStrings| == 8;
        expect |sectionStrings| == 8;
        assume {:axiom} |sectionStrings[0]| > 6;
        expect |sectionStrings[0]| > 6;
        var seedString := sectionStrings[0][7..];
        seeds := Map(x => abs(Integer(x)), split(seedString, " "));
        print seeds;
        for i:=1 to |sectionStrings| {
            assume {:axiom} |splitOnBreak(sectionStrings[i])| > 0;
            expect |splitOnBreak(sectionStrings[i])| > 0;
            var mapString := splitOnBreak(sectionStrings[i])[1..];
            var sections : seq<seq<nat>> := [];
            for k := 0 to |mapString| {
                if mapString[k] != "" {
                    sections := sections + [Map(x => abs(Integer(x)), split(mapString[k], " "))];
                }
            }
            print sections;
            assume {:axiom} forall x :: x in sections ==> |x| == 3;
            maps := maps + [rangeMapper(sections)];
        }
    }

    method parseInput2(input:string) returns (seeds: seq<(nat, nat)>, maps: seq<nat -> nat>) {
        maps :=[];
        seeds := [];
        var sectionStrings := splitOnDoubleBreak(input);
        assume {:axiom} |sectionStrings| == 8;
        expect |sectionStrings| == 8;
        assume {:axiom} |sectionStrings[0]| > 6;
        expect |sectionStrings[0]| > 6;
        var seedString := sectionStrings[0][7..];
        var seedsseq := Map(x => abs(Integer(x)), split(seedString, " "));
        for i := 0 to |seedsseq|/2 {
            seeds := seeds + [(seedsseq[2*i], seedsseq[2*i+1])];
        }
        print seeds, "\n";
        for i:=1 to |sectionStrings| {
            assume {:axiom} |splitOnBreak(sectionStrings[i])| > 0;
            expect |splitOnBreak(sectionStrings[i])| > 0;
            var mapString := splitOnBreak(sectionStrings[i])[1..];
            var sections : seq<seq<nat>> := [];
            for k := 0 to |mapString| {
                if mapString[k] != "" {
                    sections := sections + [Map(x => abs(Integer(x)), split(mapString[k], " "))];
                }
            }
            print sections, "\n";
            assume {:axiom} forall x :: x in sections ==> |x| == 3;
            maps := maps + [rangeMapper(sections)];
        }
    }


    method problem5_1(input: string) returns (x: int) {
        var seeds, functs := parseInput(input);
        assume {:axiom} |functs| > 1;
        print "\n", functs[0](48);
        print "\n", "GOTHERE?";
        // print "\n", maps[0](51);
        // print "\n", maps[0](97);
        // print "\n", maps[0](98);
        // print "\n", maps[0](99);
        var locations := Map((seed: nat) => FoldLeft((x: nat, f: nat -> nat) => f(x), seed, functs), seeds);
        print locations, "\nresult: ";
        assume {:axiom} |locations| > 0;
        return FoldLeft(min, locations[0], locations);
    }

    method problem5_2(input: string) returns (x: int) {
        var seeds, functs := parseInput2(input);
        var minLoc:Option<nat> := None;
        for i := 0 to |seeds| {
            print "\n i: ",i, " ", seeds[i];
            for k: nat := seeds[i].0 to seeds[i].0+seeds[i].1 {
                var loc: nat := FoldLeft((x: nat, f: nat -> nat) => f(x), k, functs);
                match minLoc {
                    case None => {
                        minLoc := Some(loc);
                    }
                    case Some(minloc) => {
                        if loc < minloc {
                            minLoc := Some(loc);
                        }
                    }
                }
            }
        }
        print "\n";
        return minLoc.UnwrapOr(0);
    }
}
