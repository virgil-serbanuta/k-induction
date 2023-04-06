module SUM-TO-N-SPEC-1
  imports IMP

  claim
    <k>
      while (I <= N) {
        Sum = Sum + I;
        I += 1;
      }
      =>
      #if ?ValI:Int <Int ValN +Int 1
        while (I <= N) {
          Sum = Sum + I;
          I += 1;
        }
      #else
        .K
      #fi
      ...
    </k>
    <state>
      I |-> (0 => ?ValI:Int)
      N |-> ValN:Int
      Sum |-> ( 0 =>
                #if ?ValI:Int <Int ValN +Int 1
                #then (?ValI *Int (?ValI -Int 1) / 2)
                #else (ValN *Int (ValN +Int 1) / 2)
                #fi
              )
    </state>
    requires ?ValI:Int <=Int ValN +Int 1
endmodule
