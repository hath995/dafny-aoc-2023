include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
include "../../libraries/src/dafny/Collections/Seqs.dfy"
include "../../libraries/src/Wrappers.dfy"
module Problem8 {
    import opened Split
    import opened ParseInt
    import opened Dafny.Collections.Seq
    import opened Wrappers
    datatype Direction = Left | Right
    datatype State = State(name: string, exits: (string, string))
    method parseInput(input: string) returns (steps: seq<Direction>, states: seq<State>) {
        states := [];
        var lines := splitOnDoubleBreak(input);
        assume {:axiom} |lines| == 2;
        expect |lines| == 2;
        steps := Map((letter: string) => match letter {
            case "L" => Left
            case "R" => Right
            case _ => Left
        }, split(lines[0], ""));
        var stateLines := splitOnBreak(lines[1]);
        for i := 0 to |stateLines| {
            if stateLines[i] != "" {
                assume {:axiom} |stateLines[i]| == 16;
                expect |stateLines[i]| == 16;
                var name := stateLines[i][0..3];
                var le := stateLines[i][7..10];
                var re := stateLines[i][12..15];
                states := states + [State(name, (le, re))];
            }
        }

    }

    method problem8_1(input: string) returns (x: int) 
        decreases *
    {
        var steps, states := parseInput(input);
        assume {:axiom} |steps| > 0;
        expect |steps| > 0;
        var stateMap: map<string, State> := map[];
        print steps, "\n";
        print states, "\n";
        for i := 0 to |states| {
            stateMap := stateMap[states[i].name := states[i]];
        }
        assume {:axiom} "AAA" in stateMap;
        expect "AAA" in stateMap;
        var state := stateMap["AAA"];
        var step := 0; 
        while state.name != "ZZZ" 
            decreases *
        {
            var next := match steps[step % |steps|] {
                case Left => state.exits.0
                case Right => state.exits.1
            };

            assume {:axiom} next in stateMap;
            expect next in stateMap;
            state := stateMap[next];
            step := step + 1;
        }
        return step;
    }

    predicate EndState(states: seq<State>) 
        requires forall i :: 0 <= i < |states| ==> |states[i].name| > 0;
    {
        forall i :: 0 <= i < |states| ==> states[i].name[|states[i].name|-1] == 'Z'
    }

    method problem8_2(input: string) returns (x: int) 
        decreases *
    {
        var steps, states := parseInput(input);
        assume {:axiom} |steps| > 0;
        assume {:axiom} forall i :: 0 <= i < |states| ==> |states[i].name| > 0;
        expect |steps| > 0;
        var stateMap: map<string, State> := map[];
        print |steps|, "\n";
        print |states|, "\n";
        for i := 0 to |states| {
            stateMap := stateMap[states[i].name := states[i]];
        }
        var statelist: seq<State> := Filter((s: State) requires |s.name| > 0 => s.name[|s.name|-1]=='A', states);
        var cycles: seq<set<State>> := seq(|statelist|, i => {});
        print statelist;
        print "Starting state Count:= ", |statelist|, "\n";

        var step := 0; 
        // while !EndState(statelist)
        //     decreases *
        // {
        //     var nextList: seq<State> := [];
        //     for i := 0 to |statelist| {

        //         var next := match steps[step % |steps|] {
        //             case Left => statelist[i].exits.0
        //             case Right => statelist[i].exits.1
        //         };

        //         assume {:axiom} next in stateMap;
        //         expect next in stateMap;
        //         nextList := nextList+[stateMap[next]];
        //     }
        //     statelist := nextList;
        //     step := step + 1;
        // }
        return step;
    }
}
