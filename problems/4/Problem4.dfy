include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
include "../../libraries/src/dafny/Collections/Seqs.dfy"
include "../../libraries/src/Wrappers.dfy"
module Problem4 {
    import opened Split
    import opened ParseInt
    import opened Dafny.Collections.Seq
    import opened Wrappers

    datatype Game = Game(id: int, winning: seq<int>, cards: seq<int>)
    method parseInput(input: string) returns (games: seq<Game>) {
        var lines := Filter(x => x != "", splitOnBreak(input));
        games :=[];
        for i := 0 to |lines| {
            var headerBatch := split(lines[i], ":");
            assume {:axiom} |headerBatch| == 2;
            expect |headerBatch| == 2;
            var isString := split(headerBatch[0], " ");
            assume {:axiom} |isString| > 0;
            expect {:axiom} |isString| > 0;
            var id := Integer(isString[|isString|-1]);
            var numStrings := split(headerBatch[1], "|");
            assume {:axiom} |numStrings| == 2;
            expect {:axiom} |numStrings| == 2;
            var winningStrings := split(numStrings[0], " ");
            var cardStrings := split(numStrings[1], " ");

            var winning := Map(Integer, Filter(x => x != "", winningStrings));
            var cards := Map(Integer, Filter(x => x != "", cardStrings));
            games := games + [Game(id, winning, cards)];
        }
    }

    function abs(x: int): nat {
        if x < 0 then -x else x
    }

    function exp(base: int, pow: nat): int {
        if pow == 0 then 1 else base * exp(base, pow-1)
    }

    method problem4_1(input: string) returns (x: int) {
        var data := parseInput(input);
        var scores := Map((game: Game) =>
            var winning := set x | x in game.winning;
            var cards := set x | x in game.cards;
            var matchings := winning * cards;
            if |matchings| == 0 then 0 else exp(2, |matchings|-1)
        , data);
        // print scores;
        return FoldLeft((a,b)=> a+b, 0, scores);
    }

    method problem4_2(input: string) returns (x: int) 
    decreases *
    {
        var data := parseInput(input);
        var gameMap: map<int, Game> := map[];
        var gameWinnings: map<int, nat> := map[];
        for i := 0 to |data| {
            gameMap := gameMap[data[i].id := data[i]];
            var winning := set x | x in data[i].winning;
            var cards := set x | x in data[i].cards;
            var matchings := winning * cards;
            // var copies := seq(|matchings|, k => data[i].id+k+1);
            gameWinnings := gameWinnings[data[i].id := |matchings|];
        }
        // print gameMap;
        x := |data|;
        var scratchcards: array<int> := ToArray(Map((x: Game) => 1, data));
        for i := 0 to scratchcards.Length
        {
            while scratchcards[i] > 0 
                decreases *
            {
                assume {:axiom} i+1 in gameWinnings;
                for k := 1 to gameWinnings[i+1]+1 
                    // invariant scratchcards[i] == old(scratchcards[i])
                {
                    assume {:axiom} i+k < scratchcards.Length;
                    scratchcards[i+k] := scratchcards[i+k]+1;
                    x := x + 1;
                }
                scratchcards[i] := scratchcards[i] -1;
            }
        }
    }
}
