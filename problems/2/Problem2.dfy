include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
include "../../libraries/src/dafny/Collections/Seqs.dfy"
module Problem2 {
    import opened Split
    import opened ParseInt
    import opened Dafny.Collections.Seq

    datatype Ball = Blue | Red | Green
    predicate possibleGame(game: seq<multiset<Ball>>, limit: multiset<Ball>) {
        forall i :: 0 <= i < |game| ==> game[i] <= limit
    }
    datatype Game = Game(id: int, cubeSets: seq<multiset<Ball>>)
    method parseInput(input: string) returns (gameList: seq<Game>)

    {
        gameList :=[];
        var gameStrings := splitOnBreak(input);
        for i:=0 to |gameStrings| {
            if gameStrings[i] != "" {
                assume {:axiom} |split(gameStrings[i], ":")| > 1;
                expect |split(gameStrings[i], ":")| > 1, "Game id was not properly parsed";
                var gamePrepString :=  split(gameStrings[i], ":");
                assume {:axiom} |gamePrepString| > 1;
                expect  |gamePrepString| > 1;
                assume {:axiom} |split(gamePrepString[0], " ")| > 1;
                var id := Integer(split(gamePrepString[0], " ")[1]);
                var gameSetStrings := split(gamePrepString[1], ";");
                var games: seq<multiset<Ball>> := [];
                for k := 0  to |gameSetStrings| {
                    var ballset: multiset<Ball> := multiset{};
                    var ballStrings := split(gameSetStrings[k], ",");
                    for j := 0 to |ballStrings| {
                        assume {:axiom} |ballStrings[j]| > 1;
                        var color_count := split(ballStrings[j][1..], " ");
                        assume {:axiom} |color_count| == 2;
                        var count := Integer(color_count[0]);
                        var color: Ball := match color_count[1] {
                            case "red" => Red
                            case "blue" => Blue
                            case "green" => Green
                            case _ => Red
                        };
                        assume {:axiom} count >= 0;
                        ballset := ballset[color := count];
                    }
                    games := games + [ballset];
                }
                gameList := gameList + [Game(id, games)];
            }
        }
    }

    method problem2_1(input: string) returns (x: int) {
        var limit: multiset<Ball> := multiset{};
        limit := limit[Red:=12];
        limit := limit[Blue:=14];
        limit := limit[Green:=13];
        var data := parseInput(input);
        var valid := Filter((game: Game) => possibleGame(game.cubeSets, limit), data);
        return FoldLeft((a: int, b: Game)=>a+b.id,0, valid);
    }

    function mspower(ms: multiset<Ball>): int {
        (if Red in ms then ms[Red] else 1) * 
        (if Blue in ms then ms[Blue] else 1) *
        (if Green in ms then ms[Green] else 1)
    }

    function msmax(ams: multiset<Ball>, bms: multiset<Ball>): multiset<Ball> 
    {
        var ms: multiset<Ball> := multiset{}; 
        (if ams[Red] > bms[Red] then ms[Red := ams[Red]] else ms[Red := bms[Red]]) +
        (if ams[Blue] > bms[Blue] then ms[Blue := ams[Blue]] else ms[Blue := bms[Blue]]) +
        (if ams[Green] > bms[Green] then ms[Green := ams[Green]] else ms[Green := bms[Green]])
    }

    method problem2_2(input: string) returns (x: int) {
        var data := parseInput(input);
        // var sets := Map((game: Game) => assume {:axiom} |game.cubeSets| > 0; FoldLeft((x,y) => msmax(x, y), game.cubeSets[0], game.cubeSets),data);
        // print sets;
        var powers := Map((game: Game) => assume {:axiom} |game.cubeSets| > 0; mspower(FoldLeft((x,y) => msmax(x , y), game.cubeSets[0], game.cubeSets)),data);
        // print powers;
        var result := FoldLeft((a,b)=> a+b, 0,powers);
        return result;
    }
}