include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
include "../../libraries/src/dafny/Collections/Seqs.dfy"
include "../../libraries/src/Wrappers.dfy"
module Problem11 {
    import opened Split
    import opened ParseInt
    import opened Dafny.Collections.Seq
    import opened Wrappers

    type Point = (nat, nat)
    function abs(x: int): nat {
        if x < 0 then -x else x
    }

    predicate allEmpty(row: seq<string>) {
        forall i :: 0 <= i < |row| ==> row[i] == "."
    }

    predicate allEmptyColumn(grid: seq<seq<string>>, x: int) {
        forall i :: 0 <= i < |grid| ==> 0 <= x < |grid[i]| && grid[i][x] == "."
    }

    method parseInput2(input: string) returns (galaxies: seq<Point>)

    {
        var lines := splitOnBreak(input);
        var grid := Map(x => split(x,""), Filter(x=>x != "", lines));
        assume {:axiom} |grid| > 0;
        var emptyrows := set i | 0 <= i < |grid| && allEmpty(grid[i]);
        var emptycolumns := set i | 0 <= i < |grid[0]| && allEmptyColumn(grid, i);
        var expansion := 1000000-1; //-1 to not overcount the row
        galaxies := [];
        for y := 0 to |grid| {
            for x := 0 to |grid[y]| {
                if grid[y][x] == "#" {
                    var yoffset := |set i | 0 <= i < y && i in emptyrows | * expansion;
                    var xoffset := |set i |  0 <= i < x && i in emptycolumns| * expansion;
                    galaxies := galaxies + [(x+xoffset, y+yoffset)];
                }
            }
        }
    }

    method parseInput(input: string) returns (galaxies: seq<Point>)

    {
        var lines := splitOnBreak(input);
        var grid := Map(x => split(x,""), Filter(x=>x != "", lines));
        assume {:axiom} |grid| > 0;
        var emptyrows := set i | 0 <= i < |grid| && allEmpty(grid[i]);
        var emptycolumns := set i | 0 <= i < |grid[0]| && allEmptyColumn(grid, i);
        // print grid, "\n";
        // print emptyrows, "\n";
        // print emptycolumns, "\n";
        galaxies := [];
        for y := 0 to |grid| {
            for x := 0 to |grid[y]| {
                if grid[y][x] == "#" {
                    var yoffset := |set i | 0 <= i < y && i in emptyrows |;
                    var xoffset := |set i |  0 <= i < x && i in emptycolumns|;
                    // print xoffset, " ", yoffset, "\n";
                    // print "pt: ", (x+xoffset, y+yoffset), "\n";
                    galaxies := galaxies + [(x+xoffset, y+yoffset)];
                }
            }
        }
    }

    function distance(a: Point, b: Point): nat {
        abs(a.0-b.0)+abs(a.1-b.1)
    }

    method problem11_1(input: string) returns (x: int) {
        var galaxies := parseInput(input);
        assume {:axiom} |galaxies| > 0;
        // print "dist 1,7 ", distance(galaxies[0],galaxies[6]), "\n";
        // print "dist 3,6 ", distance(galaxies[2],galaxies[5]), "\n";
        // print "dist 8,9 ", distance(galaxies[7],galaxies[8]), "\n";
        x := 0;
        for i := 0 to |galaxies|-1 {
            for j := i + 1 to |galaxies| {
                x := x + distance(galaxies[i], galaxies[j]);
            }
        }
    }

    method problem11_2(input: string) returns (x: int) {
        var galaxies := parseInput2(input);
        assume {:axiom} |galaxies| > 0;
        x := 0;
        for i := 0 to |galaxies|-1 {
            for j := i + 1 to |galaxies| {
                x := x + distance(galaxies[i], galaxies[j]);
            }
        }
    }
}
