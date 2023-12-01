include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
include "../../libraries/src/dafny/Collections/Seqs.dfy"
module Problem1 {
    import opened Split
    import opened ParseInt
    import opened Dafny.Collections.Seq

    method parseInput1(input: string) returns (data: seq<int>) {
        data := [];
        var lines := Filter(line => line != "", splitOnBreak(input));
        var numberStrings := Map(line => Filter(charInNC, line),lines);
        var calibration := Map(line=>
            assume {:axiom}  |line| >= 2;
            [line[0], line[|line|-1]], numberStrings);
        data := Map(Integer, calibration);
    }

    function parseElfDigits(input: string, result: seq<char>): seq<char> {
        if |input| == 0 then result else
            if "one" <= input then
                parseElfDigits(input[1..], result+['1'])
            else if "two" <= input then
                parseElfDigits(input[1..], result+['2'])
            else if "three" <= input then
                parseElfDigits(input[1..], result+['3'])
            else if "four" <= input then
                parseElfDigits(input[1..], result+['4'])
            else if "five" <= input then
                parseElfDigits(input[1..], result+['5'])
            else if "six" <= input then
                parseElfDigits(input[1..], result+['6'])
            else if "seven" <= input then
                parseElfDigits(input[1..], result+['7'])
            else if "eight" <= input then
                parseElfDigits(input[1..], result+['8'])
            else if "nine" <= input then
                parseElfDigits(input[1..], result+['9'])
            else if charInNC(input[0]) then
                parseElfDigits(input[1..], result+[input[0]])
            else
                parseElfDigits(input[1..], result)

    }
    
    method parseInput2(input: string) returns (data: seq<int>) {
        data := [];
        var lines := Filter(line => line != "", splitOnBreak(input));
        var numberStrings := Map(line => parseElfDigits(line,[]),lines);
        print numberStrings,"\n\n";
        var calibration := Map(line=>
            assume {:axiom}  |line| >= 2;
            // if |line| == 1 then [line[0]] else
            [line[0], line[|line|-1]], numberStrings);
        data := Map(Integer, calibration);
    }

    method problem1_1(input: string) returns (x: int)
    {
        var data := parseInput1(input);
        print data, "\n";
        return FoldLeft((a,b)=>a+b, 0, data);
    }

    method problem1_2(input: string) returns (x: int)
    {
        var data := parseInput2(input);
        print data, "\n";
        return FoldLeft((a,b)=>a+b, 0, data);
    }
}