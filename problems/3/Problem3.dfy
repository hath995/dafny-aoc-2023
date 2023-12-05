include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
include "../../libraries/src/dafny/Collections/Seqs.dfy"
include "../../libraries/src/Wrappers.dfy"
module Problem3 {
    import opened Split
    import opened ParseInt
    import opened Dafny.Collections.Seq
    import opened Wrappers
    type Point = (nat, nat)
    datatype Gear = Gear(val: int, length: nat, pos: Point)



    method parseInput(input: string) returns (gears: seq<Gear>, symbols: set<Point>)
    {
        gears := [];
        symbols := {};
        var lines := splitOnBreak(input);
        for i:nat := 0 to |lines| {
            var lineGears: seq<Gear> := [];
            var partialNum: string := "";
            var numStart: Option<Point> := None;
            for k:nat := 0 to |lines[i]| {
                if charInNC(lines[i][k]) && lines[i][k] != '-' {
                    partialNum := partialNum + [lines[i][k]];
                    if numStart.None? {
                        numStart := Some((k,i));
                    }
                }else{
                    if |partialNum| > 0 {
                        lineGears := lineGears + [Gear(Integer(partialNum), |partialNum|, numStart.UnwrapOr((0,0)))];
                        partialNum := "";
                        numStart := None;
                    }
                    if lines[i][k] != '.' {
                        symbols := symbols + {(k,i)};
                    }
                }
            }

            if |partialNum| > 0 {
                lineGears := lineGears + [Gear(Integer(partialNum), |partialNum|, numStart.UnwrapOr((0,0)))];
                partialNum := "";
                numStart := None;
            }
            gears := gears + lineGears;
        }
    }

    method parseInput2(input: string) returns (gears: seq<Gear>, symbols: set<Point>)
    {
        gears := [];
        symbols := {};
        var lines := splitOnBreak(input);
        for i:nat := 0 to |lines| {
            var lineGears: seq<Gear> := [];
            var partialNum: string := "";
            var numStart: Option<Point> := None;
            for k:nat := 0 to |lines[i]| {
                if charInNC(lines[i][k]) && lines[i][k] != '-' {
                    partialNum := partialNum + [lines[i][k]];
                    if numStart.None? {
                        numStart := Some((k,i));
                    }
                }else{
                    if |partialNum| > 0 {
                        lineGears := lineGears + [Gear(Integer(partialNum), |partialNum|, numStart.UnwrapOr((0,0)))];
                        partialNum := "";
                        numStart := None;
                    }
                    if lines[i][k] == '*' {
                        symbols := symbols + {(k,i)};
                    }
                }
            }

            if |partialNum| > 0 {
                lineGears := lineGears + [Gear(Integer(partialNum), |partialNum|, numStart.UnwrapOr((0,0)))];
                partialNum := "";
                numStart := None;
            }
            gears := gears + lineGears;
        }
    }

    function neighborSet(gear: Gear): set<Point> {
        // set i | gear.pos.1-1 >=0 && 0 < gear.pos.0-1 <= i <= gear.pos.0+gear.length+1 :: (gear.pos.1-1,i)
        set j,i |  gear.pos.1-1 <= j <= gear.pos.1+1 && 0 <= j &&  gear.pos.0-1 <= i <= gear.pos.0+gear.length && 0 <= i :: (i,j)
    }

    predicate NextToSymbol(gear: Gear, symbols: set<Point>) {
        neighborSet(gear) * symbols != {}
    }

    method problem3_1(input: string) returns (x: int) {
        var gears, symbols := parseInput(input);
        // print gears, "\n\n";
        // print Map(neighborSet, gears), "\n\n";
        print symbols, "\n\n";
        var gearmap: map<Point, Gear> := map[];
        for i := 0 to |gears| {
            gearmap := gearmap[gears[i].pos := gears[i]];
        }
        var nextTo := Filter((gear: Gear) => NextToSymbol(gear, symbols), gears);
        var notnextTo := Filter((gear: Gear) => !NextToSymbol(gear, symbols), gears);
        //https://www.shellhacks.com/bash-colors/
        var RL_START_IGNORE := 1 as char;
        var RL_END_IGNORE := 2 as char;
        var escape: char := 27 as char;
        var RED:=[RL_START_IGNORE]+[escape]+"[1;31m"+[RL_END_IGNORE];
        var BLUE:=[RL_START_IGNORE]+[escape]+"[1;34m"+[RL_END_IGNORE];
        var GREEN:=[RL_START_IGNORE]+[escape]+"[1;32m"+[RL_END_IGNORE];
        var NOCOLOR:=[RL_START_IGNORE]+[escape]+"[0m"+[RL_END_IGNORE];
        // print [RL_START_IGNORE]+[escape]+"[1;31m"+[RL_END_IGNORE];
        // print notnextTo, "\n";
        var lines := splitOnBreak(input);
        var sum := 0;
        var y :=0;
        while y < |lines| {
            var x:=0;
            while x < |lines[0]| {
                if (x,y) in symbols {
                    assume {:axiom} 0 <= x < |lines[y]|;
                    print BLUE, lines[y][x], NOCOLOR;
                }else if (x,y) in gearmap.Keys {
                    if NextToSymbol(gearmap[(x,y)], symbols) {
                        print GREEN, gearmap[(x,y)].val, NOCOLOR;
                        sum := sum + gearmap[(x,y)].val;
                        x := x + gearmap[(x,y)].length-1;
                    }else{
                        print RED, gearmap[(x,y)].val, NOCOLOR;
                        x := x + gearmap[(x,y)].length-1;
                    }
                }else{
                    print ".";
                }
                x := x + 1;
            }
            print "\n";
            y := y + 1;
        }
        // return FoldLeft((sum: int, gear: Gear) => sum+gear.val, 0, nextTo);
        return sum;
    }

    method problem3_2(input: string) returns (x: int) {
        var RL_START_IGNORE := 1 as char;
        var RL_END_IGNORE := 2 as char;
        var escape: char := 27 as char;
        var RED:=[RL_START_IGNORE]+[escape]+"[1;31m"+[RL_END_IGNORE];
        var BLUE:=[RL_START_IGNORE]+[escape]+"[1;34m"+[RL_END_IGNORE];
        var GREEN:=[RL_START_IGNORE]+[escape]+"[1;32m"+[RL_END_IGNORE];
        var NOCOLOR:=[RL_START_IGNORE]+[escape]+"[0m"+[RL_END_IGNORE];

        var gears, symbols := parseInput2(input);
        var gearmap: map<Point, Gear> := map[];
        for i := 0 to |gears| {
            gearmap := gearmap[gears[i].pos := gears[i]];
        }
        var lines := splitOnBreak(input);
        var sum := 0;
        var y :=0;
        var pairs: map<Point, seq<Gear>> := map[];
        while y < |lines| {
            var x:=0;
            while x < |lines[0]| {
                if (x,y) in symbols {
                    assume {:axiom} 0 <= x < |lines[y]|;
                    print BLUE, lines[y][x], NOCOLOR;
                }else if (x,y) in gearmap.Keys {
                    if NextToSymbol(gearmap[(x,y)], symbols) {
                        var symbol :| symbol in neighborSet(gearmap[(x,y)]) * symbols;
                        if symbol in pairs {
                            pairs := pairs[symbol := pairs[symbol]+[gearmap[(x,y)]]];
                            assume {:axiom} |pairs[symbol]| == 2;
                            sum := sum + pairs[symbol][0].val * pairs[symbol][1].val;
                            // print "sum + ", pairs[symbol][0].val * pairs[symbol][1].val;
                        }else{
                            pairs := pairs[symbol := [gearmap[(x,y)]]];
                        }
                        print GREEN, gearmap[(x,y)].val, NOCOLOR;
                        // sum := sum + gearmap[(x,y)].val;
                        x := x + gearmap[(x,y)].length-1;
                    }else{
                        print RED, gearmap[(x,y)].val, NOCOLOR;
                        x := x + gearmap[(x,y)].length-1;
                    }
                }else{
                    print ".";
                }
                x := x + 1;
            }
            print "\n";
            y := y + 1;
        }
        // print pairs;
        return sum;
    }
}
