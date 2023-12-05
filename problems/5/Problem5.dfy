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
        // ensures forall x:nat :: rangeMapper(range).requires(x)
    {
        var m: nat -> nat := (x: nat) => if |range| == 0 then 
            x
        else if range[0][1] <= x < range[0][1]+range[0][2] then 
            range[0][0]+(x-range[0][1])
        else 
            rangeMapper(range[1..])(x);
        m
    }
    // function rangeMapper(range: seq<seq<nat>>): nat -> nat {
    //     (z: nat) => z
    // }
    ghost function RangeToSet(pair: Range): set<nat>
    {
        // set i {:autotriggers false} | pair.0 <= i < pair.1 :: i
        set i | pair.0 <= i < pair.1 :: i
    }

    lemma RangeToSetSize(pair: Range)
        ensures |RangeToSet(pair)| == pair.1-pair.0
        decreases pair.1-pair.0
    {
        if pair.1-pair.0 == 0 {
            assert false;
        }if pair.1-pair.0 == 1 {
            assert pair.0 in RangeToSet(pair);
            assert pair.1 !in RangeToSet(pair);
            var left := RangeToSet(pair);
            assert left == {pair.0};
            assert |RangeToSet(pair)| == 1;
        }else {
            var left := RangeToSet(pair);
            assert RangeToSet(pair) == {pair.1-1}+RangeToSet((pair.0,pair.1-1));
            RangeToSetSize((pair.0,pair.1-1));

        }
    }

    lemma RangeToSetEqual(pair1: Range, pair2: Range) 
        requires pair1.1-pair1.0 == pair2.1-pair2.0
        ensures |RangeToSet(pair1)| == |RangeToSet(pair2)|
    {
        RangeToSetSize(pair1);
        RangeToSetSize(pair2);
    }

    ghost function SeqToSet(sequence: seq<Range>): set<nat>
        decreases |sequence|
    {
        if |sequence| == 0 then {}
        else if |sequence| == 1 then RangeToSet(sequence[0])
        else RangeToSet(sequence[0]) + SeqToSet(sequence[1..])
    }

    ghost function seqSetSize(sequence: seq<Range>): nat {
        if |sequence| == 0 then 0 else |RangeToSet(sequence[0])| + seqSetSize(sequence[1..])
    }

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
    type NatRange = (nat, nat)
    predicate IsRange(r: NatRange) {
        r.0 < r.1
    }
    type Range = x: NatRange | IsRange(x) witness (0,1)
    datatype Mapper = Mapper(r: Range, dest: nat)
    method parseInput2(input:string) returns (seeds: seq<Range>, maps: seq<seq<Mapper>>) {
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
            assume {:axiom} seedsseq[2*i+1] > 0;
            expect seedsseq[2*i+1] > 0;
            assert seedsseq[2*i] < seedsseq[2*i]+ seedsseq[2*i+1];
            assert IsRange((seedsseq[2*i], seedsseq[2*i]+ seedsseq[2*i+1]));
            seeds := seeds + [(seedsseq[2*i], seedsseq[2*i]+ seedsseq[2*i+1])];
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
            assume {:axiom} forall x :: x in sections ==> |x| == 3 && x[2]>0;
            var mappers := Map(section requires section in sections => 
            assert section in sections;
            Mapper((section[1], section[1]+section[2]), section[0]), sections);
            print sections, "\n";
            maps := maps + [(mappers)];
        }
    }



    function applyMappers(r: Range, mapper: Mapper): seq<Range> {
        [r]
    }

    predicate InMapperRange(r: Range, mapper: Mapper) {
        mapper.r.0 <= r.0 < r.1 <= mapper.r.1
    }

    predicate InRange(inner: Range, outer: Range) {
        outer.0 <= inner.0 < inner.1 <= outer.1
    }

    function applyMapperIncl(r: Range, mapper: Mapper): Range 
        requires InMapperRange(r, mapper)
    {
       (mapper.dest+(r.0 - mapper.r.0), mapper.dest +(r.1-mapper.r.0))
    }

    predicate IsMappedRange(r: Range, mapper: Mapper, mr: Range) {
        InMapperRange(r, mapper) && InRange(mr, applyMapperIncl(r, mapper))
    }

    function max(a: nat, b: nat): nat {
        if a <= b then b else a
    }

    predicate NoOverlap(r: Range, mapper: Mapper) {
        (r.1 <= mapper.r.0) || (mapper.r.1 <= r.0) 
    }

    function overlap(r: Range, mapper: Mapper): Range 
        requires !NoOverlap(r, mapper)
        ensures InRange(overlap(r, mapper), r)
        ensures InRange(overlap(r, mapper), mapper.r)
    {
        assert max(r.0, mapper.r.0) < min(r.1, mapper.r.1);
        (max(r.0, mapper.r.0), min(r.1, mapper.r.1))
    }
     
    method test() 
    {
        assert applyMapperIncl((98,100), Mapper((98,100),50)) == (50,52);
        assert applyMapperIncl((98,100), Mapper((98,100),1)) == (1,3);
        assert overlap((98,100), Mapper((98,100),1)) == (98,100);
        assert overlap((1,100), Mapper((10,20),1)) == (10,20);
        assert overlap((1,20), Mapper((10,30),1)) == (10,20);
        assert overlap((1,20), Mapper((1,30),1)) == (1,20);
    }

    method apMapper(r: Range, mapper: Mapper) returns (mapped: seq<Range>, unmapped: seq<Range>)
        ensures |RangeToSet(r)| == seqSetSize(mapped+unmapped)
        ensures forall x :: x in unmapped ==> InRange(x, r)
        ensures NoOverlap(r, mapper) ==> mapped == []
        ensures !NoOverlap(r, mapper) ==> forall x :: x in mapped ==> IsMappedRange(overlap(r, mapper), mapper, x)
    {
        mapped := [];
        unmapped := [];
        // R |--| M |--| 
        if r.1 <= mapper.r.0 {
            unmapped := [r];
            assert |RangeToSet(r)| == seqSetSize(mapped+unmapped);
        }else if mapper.r.1 <= r.0 {
        // M |--| R |--| 
            unmapped := [r];
            assert |RangeToSet(r)| == seqSetSize(mapped+unmapped);
        }else if mapper.r.0 <= r.0 < r.1 <= mapper.r.1 {
        // M |----------| 
        // R    |--|
            assert !NoOverlap(r, mapper);
            mapped := [(mapper.dest+(r.0-mapper.r.0), mapper.dest+(r.1-mapper.r.0))];
            assert mapped[0] == applyMapperIncl(overlap(r,mapper), mapper);
            RangeToSetEqual(r, mapped[0]);
            assert |RangeToSet(r)| == seqSetSize(mapped+unmapped);
            assert |RangeToSet(r)| == |SeqToSet(mapped+unmapped)|;
        }else if r.0 < mapper.r.0 < mapper.r.1 < r.1 {
        // M    |---| 
        // R |---------|
            unmapped := [(r.0, mapper.r.0), (mapper.r.1, r.1)];
            mapped := [(mapper.dest, mapper.dest+(mapper.r.1-mapper.r.0))];
            assert mapped[0] == applyMapperIncl(overlap(r, mapper), mapper);
            RangeToSetSize(r);
            RangeToSetSize(unmapped[0]);
            RangeToSetSize(unmapped[1]);
            RangeToSetSize(mapped[0]);
            assert r.1-r.0 == unmapped[0].1-unmapped[0].0 + unmapped[1].1-unmapped[1].0 + mapped[0].1-mapped[0].0;
            calc {
                |RangeToSet(r)|;
                r.1-r.0;
                unmapped[0].1-unmapped[0].0 + unmapped[1].1-unmapped[1].0 + mapped[0].1-mapped[0].0;
                |RangeToSet(unmapped[0])| + |RangeToSet(unmapped[1])| + mapped[0].1-mapped[0].0;
                |RangeToSet(unmapped[0])| + |RangeToSet(unmapped[1])| + |RangeToSet(mapped[0])|;
                |RangeToSet(mapped[0])| + |RangeToSet(unmapped[0])| + |RangeToSet(unmapped[1])|;
                |RangeToSet(mapped[0])| + |RangeToSet(unmapped[0])| + seqSetSize([unmapped[1]]);
                seqSetSize(mapped+unmapped);
            }
            assert |RangeToSet(r)| == seqSetSize(mapped+unmapped);

        }else if r.0 < mapper.r.0 && mapper.r.0 < r.1 {
        //   1 10    20
        // M   |-----| 
        //       17
        // R |---|
            // assume r.0 == 1 && r.1== 17;
            // assume mapper.r.0 == 10 && mapper.r.1 == 20 && mapper.dest == 1;
            // assert r.0 < mapper.r.0 && mapper.r.0 < r.1;
            unmapped := [(r.0, mapper.r.0)];
            // assert unmapped[0] == (1,10);
            mapped := [(mapper.dest, mapper.dest+(r.1-mapper.r.0))];
            assert mapped[0] == applyMapperIncl(overlap(r,mapper), mapper);
            assert r.1-r.0 ==  mapped[0].1-mapped[0].0 + unmapped[0].1-unmapped[0].0 ;
            RangeToSetSize(r);
            RangeToSetSize(mapped[0]);
            RangeToSetSize(unmapped[0]);
            calc {
                |RangeToSet(r)|;
                r.1-r.0;
                mapped[0].1-mapped[0].0 + unmapped[0].1-unmapped[0].0;
                mapped[0].1-mapped[0].0 + seqSetSize([unmapped[0]]);
            }
            assert |RangeToSet(r)| == seqSetSize(mapped+unmapped);
        }else if mapper.r.0 <= r.0 && r.0 < mapper.r.1 && r.1 > mapper.r.1 {
        //   1  10
        // M |---| 
        //     5   20
        // R   |---|
        // Dest = 3
            // assume r.0 == 5 && r.1== 20;
            // assume mapper.r.0 == 1 && mapper.r.1 == 10 && mapper.dest == 3;
            // assert mapper.r.0 < r.0 && r.1 > mapper.r.1;
            unmapped := [(mapper.r.1,r.1)];
            // assert unmapped[0] == (10, 20);
            // assume mapper.dest > 0;
            // assert r.0-mapper.r.0 > 0;
            // assert mapper.r.1-r.0 > 0;
            mapped := [(mapper.dest+(r.0-mapper.r.0), mapper.dest+(mapper.r.1-r.0)+(r.0-mapper.r.0))];
            assert mapped[0] == applyMapperIncl(overlap(r,mapper), mapper);
            RangeToSetSize(r);
            RangeToSetSize(mapped[0]);
            RangeToSetSize(unmapped[0]);
            calc {
                |RangeToSet(r)|;
                r.1-r.0;
                mapped[0].1-mapped[0].0 + unmapped[0].1-unmapped[0].0;
                mapped[0].1-mapped[0].0 + seqSetSize([unmapped[0]]);
            }
            // assert mapped[0] == (7,12);
            assert |RangeToSet(r)| == seqSetSize(mapped+unmapped);
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

    method problem5_2(input: string) returns (x: int)
        decreases *
    {
        var seeds, functs := parseInput2(input);
        // // var test := Mapper((10,20),1);
        // var test := [3, 1,9];
        // var fn := rangeMapper([test]);
        // for i:=5 to 20 {
        //     print "\n",i," :", fn(i);

        // }
        // print seeds, "\n";
        // print functs, "\n";
        var nextRanges := seeds;
        for i:=0 to |functs| {
            var mappedNext: seq<Range> := [];
            // print "NEXTREANGES: ", nextRanges,"\n";
            // print functs[i], "\n";
            while |nextRanges| > 0 
                decreases *
            {
                // print "HERE\n";
                var apFound := false;
                for j := 0 to |functs[i]| {
                    var mapped, unmapped := apMapper(nextRanges[0], functs[i][j]);
                    // print i, " ", j, " THERE\n", nextRanges[0], "\n";
                    if |mapped| > 0 {
                        mappedNext := mappedNext + mapped;
                        nextRanges := nextRanges[1..]+unmapped;
                        apFound := true;
                        break;
                    }
                }
                if !apFound {
                    mappedNext := mappedNext+[nextRanges[0]];
                    nextRanges := nextRanges[1..];
                }
            }
            nextRanges := mappedNext;
        }
        print nextRanges;
        assume {:axiom} |nextRanges| > 0;
        var sortRanges: (Range, Range) -> Range :=(r: Range, l: Range) => (if r.0 < l.0 then r else l);
        var lowest: Range := FoldLeft(sortRanges, nextRanges[0], nextRanges);
        print "\n";
        print lowest;
        print "\n";
        return 5;
    }
}
