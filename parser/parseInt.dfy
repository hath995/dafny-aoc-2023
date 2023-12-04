module ParseInt {
    import Dafny.Collections.Seq
    function power(x: int, i: nat): int {
        if i == 0 then 1 else if i == 1 then x else x * power(x, i-1)
    }

    function integerHelper(ns: string, sum: int, negative: bool): int {
        if |ns| == 0 then if negative then 0 - sum else sum
        else if ns[0] == '-' then integerHelper(ns[1..], sum, true)
        else if 48 <= (ns[0] as int) < 58 then integerHelper(ns[1..], sum + ((ns[0] as int) - 48) * power(10, |ns|-1), negative)
        else integerHelper(ns[1..], sum, negative)
    }

    function Integer(ns: string): int {
        integerHelper(Seq.Filter(x => 48 <= (x as int) < 58,ns), 0, false)
    }

    method toInt(ns: string) returns (ret: int) 
        requires isNumString(ns)
    {
        ret := 0;
        var negative := false;
        for i := 0 to |ns| 

        {
            if ns[i] == '-' {
                negative := true;
            }else {
                ret := ret + ((ns[i] as int) - 48) * power(10, |ns|-(i+1));
            }
        }
        if negative {
            ret := 0 - ret;
        }

    }

    method toStr(num: int) returns (ret: string)
        ensures isNumString(ret)
    {
        var lookup := numchars();
        ret := "";
        var i := num;
        if num < 0 {
            ret := "-";
            i := 0 - num;
        }
        while i > 0 
            invariant isNumString(ret)
        {
            var digit := i % 10; 
            // assert lookup[digit] in numchars();
            ret := [lookup[digit]]+ret;
            i := i / 10;
        }
        return ret;
    }

    function numchars(): seq<char>
        ensures numchars() == ['0','1','2','3','4','5','6','7','8','9','-']
    {
        ['0','1','2','3','4','5','6','7','8','9','-']
    }

    predicate charInNC(c: char) {
        c in numchars()
    }

    predicate isNumString(s: string) 
    {
        s == "" || forall i  :: 0 <= i < |s| ==> charInNC(s[i])
    }

    function stripWhitespace(s: string): string {
        if |s| > 0 then if charInNC(s[0]) then [s[0]]+stripWhitespace(s[1..]) else stripWhitespace(s[1..]) else ""
    }

    export
        provides Integer
        provides toInt, toStr, isNumString, charInNC, numchars, stripWhitespace
}