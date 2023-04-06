module SUM-TO-N-SPEC
  imports IMP

  claim
    <k>
      while (I <= N) {
        Sum = Sum + I;
        I += 1;
      }
      =>
        .K
      ...
    </k>
    <state>
      (I |-> (ValI:Int => ValN +Int 1))
      (N |-> ValN:Int)
      (Sum |-> (ValSum:Int => ValN * (ValN +Int 1) /Int 2))
    </state>
    requires true
      andBool 0 <=Int ValI
      andBool ValI:Int <=Int ValN +Int 1
      andBool ValSum ==Int ValI * (ValI -Int 1) /Int 2
      andBool ValDecreasing ==Int ValN +Int 1 -Int ValI
    [decreases(ValDecreasing, _>Int_, 0)]
endmodule
