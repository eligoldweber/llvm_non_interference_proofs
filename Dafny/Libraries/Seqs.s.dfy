
module Collections__Seqs_s {

function last<T>(s:seq<T>):T
  requires |s| > 0
{
  s[|s|-1]
}

function first<T>(s:seq<T>):T
  requires |s| > 0
{
  s[0]
}

function all_but_last<T>(s:seq<T>):seq<T>
  requires |s| > 0
  ensures  |all_but_last(s)| == |s| - 1
{
  s[..|s|-1]
}

function all_but_first<T>(s:seq<T>): (t:seq<T>)
  requires |s| > 0
  ensures |all_but_first(s)| == |s| - 1
  ensures forall n :: n in t ==> n in s 
{
  s[1..]
}


}
