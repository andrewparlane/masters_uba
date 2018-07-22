    addi    $t1, $zero, 1
    j       jrtest0
    addi    $t1, $t1, 1
    addi    $t1, $t1, 1
    addi    $t1, $t1, 1
    addi    $t1, $t1, 1

jrtest0:
    nop
    nop
    nop
    nop
    la      $t0, jrtest1
    nop
    nop
    nop
    addi    $t2, $zero, 1
    jr      $t0
    addi    $t2, $t2, 1
    addi    $t2, $t2, 1
    addi    $t2, $t2, 1
    addi    $t2, $t2, 1

jrtest1:
    nop
    nop
    nop
    nop
    la      $t0, jrtest2
    nop
    nop
    addi    $t3, $zero, 1
    jr      $t0
    addi    $t3, $t3, 1
    addi    $t3, $t3, 1
    addi    $t3, $t3, 1
    addi    $t3, $t3, 1

jrtest2:
    nop
    nop
    nop
    nop
    la      $t0, jrtest3
    nop
    addi    $t4, $zero, 1
    jr      $t0
    addi    $t4, $t4, 1
    addi    $t4, $t4, 1
    addi    $t4, $t4, 1
    addi    $t4, $t4, 1

jrtest3:
    nop
    nop
    nop
    nop
    la      $t0, jrtest4
    addi    $t5, $zero, 1
    jr      $t0
    addi    $t5, $t5, 1
    addi    $t5, $t5, 1
    addi    $t5, $t5, 1
    addi    $t5, $t5, 1

jrtest4:
    nop
    nop
    nop
    addi    $t6, $zero, 1
    la      $t0, jalrtest0
    jr      $t0
    addi    $t6, $t6, 1
    addi    $t6, $t6, 1
    addi    $t6, $t6, 1
    addi    $t6, $t6, 1

jalrtest0:
    nop
    nop
    nop
    nop
    la      $t0, jalrtest1
    nop
    nop
    nop
    addi    $t7, $zero, 1
    jalr    $t0, $ra
    addi    $t7, $t7, 1
    addi    $t7, $t7, 1
    addi    $t7, $t7, 1
    addi    $t7, $t7, 1

jalrtest1:
    nop
    nop
    nop
    nop
    la      $t0, jalrtest2
    nop
    nop
    addi    $t8, $zero, 1
    jalr    $t0, $ra
    addi    $t8, $t8, 1
    addi    $t8, $t8, 1
    addi    $t8, $t8, 1
    addi    $t8, $t8, 1

jalrtest2:
    nop
    nop
    nop
    nop
    la      $t0, jalrtest3
    nop
    addi    $t9, $zero, 1
    jalr    $t0, $ra
    addi    $t9, $t9, 1
    addi    $t9, $t9, 1
    addi    $t9, $t9, 1
    addi    $t9, $t9, 1

jalrtest3:
    nop
    nop
    nop
    nop
    la      $t0, jalrtest4
    addi    $s0, $zero, 1
    jalr    $t0, $ra
    addi    $s0, $s0, 1
    addi    $s0, $s0, 1
    addi    $s0, $s0, 1
    addi    $s0, $s0, 1

jalrtest4:
    nop
    nop
    nop
    addi    $s1, $zero, 1
    la      $t0, jalrtest5
    jalr    $t0, $ra
    addi    $s1, $s1, 1
    addi    $s1, $s1, 1
    addi    $s1, $s1, 1
    addi    $s1, $s1, 1

jalrtest5:
    nop
    nop
    nop
    la      $t0, jalrtest6
    jalr    $t0, $ra
    nop
    nop
    la      $t0, jalrtest7
    jalr    $t0, $ra
    nop
    la      $t0, jalrtest8
    jalr    $t0, $ra
    la      $t0, jalrtest9
    jalr    $t0, $ra
    jalr    $t0, $ra
    jalr    $t0, $ra
    nop
    nop
    nop
    beq     $zero, $zero, combinedTest0

jalrtest6:
    nop
    nop
    nop
    jr      $ra

jalrtest7:
    nop
    nop
    jr      $ra

jalrtest8:
    nop
    jr      $ra

jalrtest9:
    jr      $ra

combinedTest0:
    nop
    nop
    nop
    la      $t0, error
    J       combinedTest1
    JR      $t0
    beq     $zero, $zero, error
    nop
    nop
    nop

combinedTest1:
    nop
    nop
    nop
    J       combinedTest2
    beq     $zero, $zero, error
    JR      $t0
    nop
    nop
    nop

combinedTest2:
    nop
    nop
    nop
    beq     $zero, $zero, combinedTest3
    JR      $t0
    J       error
    nop
    nop
    nop

combinedTest3:
    nop
    nop
    nop
    beq    $zero, $zero, combinedTest4
    J       error
    JR      $t0
    nop
    nop
    nop

combinedTest4:
    nop
    nop
    nop
    la      $t0, combinedTest5
    JR      $t0
    beq     $zero, $zero, error
    J       error
    nop
    nop
    nop

combinedTest5:
    nop
    nop
    nop
    la      $t0, combinedTest6
    JR      $t0
    J       error
    beq     $zero, $zero, error
    nop
    nop
    nop

combinedTest6:
    nop
    nop
    nop
    subi    $t1, $t1, 2
    subi    $t2, $t2, 2
    subi    $t3, $t3, 2
    subi    $t4, $t4, 2
    subi    $t5, $t5, 2
    subi    $t6, $t6, 2
    subi    $t7, $t7, 2
    subi    $t8, $t8, 2
    subi    $t9, $t9, 2
    subi    $s0, $s0, 2
    subi    $s1, $s1, 2
    bge     $t1, $zero, error
    bge     $t2, $zero, error
    bge     $t3, $zero, error
    bge     $t4, $zero, error
    bge     $t5, $zero, error
    bge     $t6, $zero, error
    bge     $t7, $zero, error
    bge     $t8, $zero, error
    bge     $t9, $zero, error
    bge     $s0, $zero, error
    bge     $s1, $zero, error
    b       doneOk

error:
    j       error
    nop
    nop
    nop

doneOk:
    j       doneOk
    nop
    nop
    nop
