
const hundred : real := 100.0;
const one : real := 1.0;
const zero : real := 0.0;

method Main() {

    print "\n Base Finding Subscore: ";
    var baseFindig := BaseFindingSubscore(0.9, 1.0, 1.0, 1.0, 1.0);
    print baseFindig;
    print "\n Attack Surface Subscore: ";
    var attackSurface := AttackSurfaceSubscore(0.9, 1.0, 1.0, 1.0, 0.9, 1.0);
    print attackSurface;
    print "\n Environmental Subscore: ";
    var environmental := EnvironmentalSubscore(0.9, 1.0, 1.0, 1.0, 1.0);
    print environmental;

    print "\n Resultado del CWSS: ";
    var base : real := baseFindig * attackSurface * environmental;
    print base;

    print "\n";
    print "\n =====================================================================";

    print "\n Llamando segundo metodo de comprobacion:";
    print "\n Total:";
    assert zero <= baseFindig <= hundred;
    assert zero <= attackSurface <= one;
    assert zero <= environmental <= one;
    var total := Total(baseFindig, attackSurface, environmental);
    print total;
    print "\n \n";

    print "\n =====================================================================";
    print "\n OTRAS PRUEBAS: \n";
    
    print "\n PRUEBA 1: TI:C,1/AP:P,0.9/AL:N,0.7/IC:M,0.7/FC:LT,0.8/    RP:RU,0.7/RL:S,0.9/AV:V,0.8/AS:N,1/IN:M,0.8/SC:P,0.1/   BI:M,0.6/DI:M,0.6/EX:M,0.6/EC:I,0.5/P:C,0.8/";
    print "\n URL: https://www.cwss-score.info/#TI:C,1/AP:P,0.9/AL:N,0.7/IC:M,0.7/FC:LT,0.8/RP:RU,0.7/RL:S,0.9/AV:V,0.8/AS:N,1/IN:M,0.8/SC:P,0.1/BI:M,0.6/DI:M,0.6/EX:M,0.6/EC:I,0.5/P:C,0.8/";
    print "\n Esperado 1: BFS: 61.6 - ASF: 0.67 - ENS: 0.315 - Total Esperado CWSS: 13.0";
    print "\n Total Esperado 1: 13.0";
    var bfs_test_1 := BaseFindingSubscore(1.0,0.9,0.7,0.7,0.8);
    var ass_test_1 := AttackSurfaceSubscore(0.7,0.9,0.8,1.0,0.8,0.1);
    var ens_test_1 := EnvironmentalSubscore(0.6,0.6,0.6,0.5,0.8);
    print "\n Obtenido 1: BFS: "; print bfs_test_1; print " - ASF: "; print ass_test_1; print " - ENS: "; print ens_test_1;
    var total1 := Total(bfs_test_1, ass_test_1, ens_test_1);
    print "\n Total 1: ";
    print total1;
    print "\n";

    print "\n PRUEBA 2: TI:C,1/AP:A,1/AL:A,1/IC:N,1/FC:F,0/  RP:L,0.9/RL:D,0.9/AV:L,0.5/AS:D,0.85/IN:D,0.55/SC:UK,0.5/   BI:D,0.6/DI:UK,0.5/EX:D,0.6/EC:M,0.7/P:W,1/";
    print "\n URL: https://www.cwss-score.info/#TI:C,1/AP:A,1/AL:A,1/IC:N,1/FC:F,0/RP:L,0.9/RL:D,0.9/AV:L,0.5/AS:D,0.85/IN:D,0.55/SC:UK,0.5/BI:D,0.6/DI:UK,0.5/EX:D,0.6/EC:M,0.7/P:W,1/";
    print "\n Esperado 1: BFS: 80.0 - ASF: 0.685 - ENS: 0.4515 - Total Esperado CWSS: 24.7";
    print "\n Total Esperado 2: 24.7";
    var bfs_test_2 := BaseFindingSubscore(1.0,1.0,1.0,1.0,0.0);
    var ass_test_2 := AttackSurfaceSubscore(0.9,0.9,0.5,0.85,0.55,0.5);
    var ens_test_2 := EnvironmentalSubscore(0.6,0.5,0.6,0.7,1.0);
    print "\n Obtenido 2: BFS: "; print bfs_test_2; print " - ASF: "; print ass_test_2; print " - ENS: "; print ens_test_2;
    var total2:= Total(bfs_test_2, ass_test_2, ens_test_2);
    print "\n Total 2: ";
    print total2;
    print "\n";

    print "\n PRUEBA 3: TODO CERO ";
    print "\n URL: https://www.cwss-score.info/#TI:Q,0/AP:Q,0/AL:Q,0/IC:Q,0/FC:Q,0/RP:Q,0/RL:Q,0/AV:Q,0/AS:Q,0/IN:Q,0/SC:Q,0/BI:Q,0/DI:Q,0/EX:Q,0/EC:Q,0/P:Q,0/";
    print "\n Esperado 1: BFS: 0.0 - ASF: 0.0 - ENS: 0.0 - Total Esperado CWSS: 0.00";
    print "\n Total Esperado 2: 0.00";
    var bfs_test_3 := BaseFindingSubscore(0.0,0.0,0.0,0.0,0.0);
    var ass_test_3 := AttackSurfaceSubscore(0.0,0.0,0.0,0.0,0.0,0.0);
    var ens_test_3 := EnvironmentalSubscore(0.0,0.0,0.0,0.0,0.0);
    print "\n Obtenido 3: BFS: "; print bfs_test_3; print " - ASF: "; print ass_test_3; print " - ENS: "; print ens_test_3;
    var total3:= Total(bfs_test_3, ass_test_3, ens_test_3);
    print "\n Total 3: ";
    print total3;
    print "\n";

    print "\n PRUEBA 4: TODOS UNO ";
    print "\n URL: https://www.cwss-score.info/#TI:C,1/AP:A,1/AL:A,1/IC:N,1/FC:T,1/RP:N,1/RL:A,1/AV:I,1/AS:N,1/IN:A,1/SC:A,1/BI:C,1/DI:H,1/EX:H,1/EC:N,1/P:W,1/";
    print "\n Esperado 1: BFS: 100.0 - ASF: 1.0 - ENS: 1.0 - Total Esperado CWSS: 100";
    print "\n Total Esperado 2: 100";
    var bfs_test_4 := BaseFindingSubscore(1.0,1.0,1.0,1.0,1.0);
    var ass_test_4 := AttackSurfaceSubscore(1.0,1.0,1.0,1.0,1.0,1.0);
    var ens_test_4 := EnvironmentalSubscore(1.0,1.0,1.0,1.0,1.0);
    print "\n Obtenido 4: BFS: "; print bfs_test_4; print " - ASF: "; print ass_test_4; print " - ENS: "; print ens_test_4;
    var total4:= Total(bfs_test_4, ass_test_4, ens_test_4);
    print "\n Total 4: ";
    print total4;
    print "\n";

    print "\n PRUEBA 5: TI:D,0.6/AP:D,0.7/AL:D,0.9/IC:D,0.6/FC:D,0.8/   RP:D,0.7/RL:D,0.9/AV:D,0.75/AS:D,0.85/IN:D,0.55/SC:D,0.7/   BI:D,0.6/DI:D,0.6/EX:D,0.6/EC:D,0.6/P:D,0.85/ ";
    print "\n URL: https://www.cwss-score.info/#TI:D,0.6/AP:D,0.7/AL:D,0.9/IC:D,0.6/FC:D,0.8/RP:D,0.7/RL:D,0.9/AV:D,0.75/AS:D,0.85/IN:D,0.55/SC:D,0.7/BI:D,0.6/DI:D,0.6/EX:D,0.6/EC:D,0.6/P:D,0.85/";
    print "\n Esperado 1: BFS: 43.2 - ASF: 0.735 - ENS: 0.3825 - Total Esperado CWSS: 12.1";
    print "\n Total Esperado 2: 12.1";
    var bfs_test_5 := BaseFindingSubscore(0.6,0.7,0.9,0.6,0.8);
    var ass_test_5 := AttackSurfaceSubscore(0.7,0.9,0.75,0.85,0.55,0.7);
    var ens_test_5 := EnvironmentalSubscore(0.6,0.6,0.6,0.6,0.85);
    print "\n Obtenido 5: BFS: "; print bfs_test_5; print " - ASF: "; print ass_test_5; print " - ENS: "; print ens_test_5;
    var total5:= Total(bfs_test_5, ass_test_5, ens_test_5);
    print "\n Total 5: ";
    print total5;
    print "\n";

    print "\n \n \n";
}

/* BASE FINDING SUBSCORE */

method TechnicalImpact(ti:real) returns (result:real) 
    requires 0.0 <= ti <= 1.0 
    ensures result >= 0.0 && result <= 10.0
{
    var technicalImpact := (10.0 * ti);
    assert technicalImpact >= 0.0 && technicalImpact <= 10.0;
    expect technicalImpact >= 0.0 && technicalImpact <= 10.0;

    result := technicalImpact;
}

method Privileges(ap:real, al:real) returns (result:real)
    requires 0.0 <= ap <= 1.0 
    requires 0.0 <= al <= 1.0 
    ensures result >= 0.0 && result <= 10.0
    ensures result == 5.0*(ap+al)
    ensures ap == 1.0 && al == 1.0 ==> result == 5.0*(ap+al)
    ensures 5.0*(ap+al) >= 0.0 && 5.0*(ap+al) <= 10.0
{
    var aquiredPrivilege := (5.0* ap);
    assert aquiredPrivilege >= 0.0 && aquiredPrivilege <= 5.0;
    expect aquiredPrivilege >= 0.0 && aquiredPrivilege <= 5.0;

    var aquiredPrivilegeLayer := (5.0 * al);
    assert aquiredPrivilegeLayer >= 0.0 && aquiredPrivilegeLayer <= 5.0;
    expect aquiredPrivilegeLayer >= 0.0 && aquiredPrivilegeLayer <= 5.0;

    result := (aquiredPrivilege + aquiredPrivilegeLayer);
    assert result >= 0.0 && result <= 10.0;
    assert result == 5.0*(ap+al);
    assert ap == 1.0 && al == 1.0 ==> result == 5.0*(ap+al);
    assert 5.0*(ap+al) >= 0.0 && 5.0*(ap+al) <= 10.0;
    expect result >= 0.0 && result <= 10.0;
    expect result == 5.0*(ap+al);
    expect ap == 1.0 && al == 1.0 ==> result == 5.0*(ap+al);
    expect 5.0*(ap+al) >= 0.0 && 5.0*(ap+al) <= 10.0;
}

method FindingConfidence(fc:real) returns (result:real)
    requires 0.0 <= fc <= 1.0
    ensures result == fc * 5.0
    ensures result >= 0.0 && result <= 5.0
    ensures fc == 1.0 ==> result == fc * 5.0
{
    var findingConfidence := (5.0 * fc); 
    assert findingConfidence >= 0.0 && findingConfidence <= 5.0;
    expect findingConfidence >= 0.0 && findingConfidence <= 5.0;

    result := findingConfidence;
    assert result >= 0.0 && result <= 5.0;
    assert result == fc * 5.0;
    assert result >= 0.0 && result <= 5.0;
    assert fc == 1.0 ==> result == fc * 5.0;
    expect result >= 0.0 && result <= 5.0;
    expect result == fc * 5.0;
    expect result >= 0.0 && result <= 5.0;
    expect fc == 1.0 ==> result == fc * 5.0;
}

method FormulaBaseAndIC(formulaBase:real, ic:real) returns (result:real)
    requires 0.0 <= ic <= 1.0
    requires formulaBase >= 0.0 && formulaBase <= 25.0
    ensures result == formulaBase * ic ==> result <= formulaBase
    ensures result >= 0.0 && result <= formulaBase
    ensures (((formulaBase * 0.01) * ic) * 100.0) <= formulaBase
{
    assert 0.0 <= ic <= 1.0;
    expect 0.0 <= ic <= 1.0;
    if ic == 1.0 {
        result := formulaBase;
    }
    else {
        var base := formulaBase * 0.01;
        var mult := base * ic;
        result := mult * 100.0;

        assert result == formulaBase * ic ==> result <= formulaBase;
        assert result >= 0.0 && result <= formulaBase;
        assert (((formulaBase * 0.01) * ic) * 100.0) <= formulaBase;
        expect result == formulaBase * ic ==> result <= formulaBase;
        expect result >= 0.0 && result <= formulaBase;
        expect (((formulaBase * 0.01) * ic) * 100.0) <= formulaBase;
    }
}

method BaseFindingSubscore(ti:real, ap:real, al:real, ic:real, fc:real) returns (baseFinding:real)
    requires 0.0 <= ti <= 1.0
    requires 0.0 <= ap <= 1.0 
    requires 0.0 <= al <= 1.0 
    requires 0.0 <= ic <= 1.0 
    requires 0.0 <= fc <= 1.0 
    ensures 0.0 <= baseFinding <= 100.0
{
    var technicalImpact := TechnicalImpact(ti);
    assert technicalImpact >= 0.0 && technicalImpact <= 10.0;
    expect technicalImpact >= 0.0 && technicalImpact <= 10.0;

    var privileges := Privileges(ap, al);
    assert privileges >= 0.0 && privileges <= 10.0;
    expect privileges >= 0.0 && privileges <= 10.0;

    var findingConficende := FindingConfidence(fc);
    assert 0.0 <= findingConficende <= 5.0;
    expect 0.0 <= findingConficende <= 5.0;

    var fti := 0.0;
    if ti == zero { fti := zero; } else {fti :=  one;}
    assert ti == zero ==> fti == 0.0;
    assert ti > zero ==> fti == 1.0;
    expect ti == zero ==> fti == 0.0;
    expect ti > zero ==> fti == 1.0;

    var formulaBase := (technicalImpact + privileges + findingConficende) * fti;
    assert formulaBase >= 0.0 && formulaBase <= 25.0;
    expect formulaBase >= 0.0 && formulaBase <= 25.0;

    var final := FormulaBaseAndIC(formulaBase, ic);
    assert 0.0 <= final <= formulaBase;

    baseFinding := final * 4.0;
    assert zero <= baseFinding <= hundred;
}

/* ATTACK SURFACE SUBSCORE */

method AttackSurfaceSubscore(rp:real, rl:real, av:real, asn:real, lin:real, sc:real) returns (attackSurface:real) 
    requires zero <= rp <= one
    requires zero <= rl <= one
    requires zero <= av <= one
    requires zero <= asn <= one
    requires zero <= lin <= one
    requires zero <= sc <= one
    ensures zero <= attackSurface <= one
{
    var formulaBase := (20.0 * (rp + rl + av)) + (20.0 * sc) + (15.0 * lin) + (5.0 * asn);
    assert 0.0 <= (20.0 * (rp + rl + av)) <= 60.0;
    assert 0.0 <= (20.0 * sc) <= 20.0;
    assert 0.0 <= (15.0 * sc) <= 15.0;
    assert 0.0 <= (5.0 * asn) <= 5.0;
    assert 0.0 <= (20.0 * (rp + rl + av)) + (20.0 * sc) + (15.0 * lin) + (5.0 * asn) <= 100.0;
    expect 0.0 <= (20.0 * (rp + rl + av)) <= 60.0;
    expect 0.0 <= (20.0 * sc) <= 20.0;
    expect 0.0 <= (15.0 * sc) <= 15.0;
    expect 0.0 <= (5.0 * asn) <= 5.0;
    expect 0.0 <= (20.0 * (rp + rl + av)) + (20.0 * sc) + (15.0 * lin) + (5.0 * asn) <= 100.0;

    var final := formulaBase * 0.01;
    assert 0.0 <= final <= 1.0;
    expect 0.0 <= final <= 1.0;

    attackSurface := final;
    assert 0.0 <= final <= 1.0;
    expect 0.0 <= final <= 1.0;
} 

/* ENVIRONMENTAL SUBSCORE */

method EnvironmentalSubscore(bi:real, di:real, ex:real, ec:real, p:real) returns (environmental:real) 
    requires zero <= bi <= one 
    requires zero <= di <= one 
    requires zero <= ex <= one 
    requires zero <= ec <= one 
    requires zero <= p <= one 
    ensures zero <= environmental <= one
{
    var formulaBase := (10.0*bi) + (3.0*di) + (4.0*ex) + (3.0*p);
    assert zero <= formulaBase <= 20.0;

    var fbi := 0.0;
    if bi == zero { fbi := zero; } else {fbi :=  one;}
    assert bi == zero ==> fbi == 0.0;
    assert bi > zero ==> fbi == 1.0;
    expect bi == zero ==> fbi == 0.0;
    expect bi > zero ==> fbi == 1.0;

    formulaBase := formulaBase * fbi;
    assert zero <= formulaBase <= 20.0;

    formulaBase := FormulaBaseAndEC(formulaBase, ec);
    assert zero <= formulaBase <= 20.0;

    environmental := formulaBase * 0.05;
    assert zero <= environmental <= one;
} 

method FormulaBaseAndEC(formulaBase:real, ec:real) returns (result:real)
    requires 0.0 <= ec <= 1.0 
    requires formulaBase >= 0.0 && formulaBase <= 20.0
    ensures result == formulaBase * ec ==> result <= formulaBase
    ensures result >= 0.0 && result <= formulaBase
    ensures (((formulaBase * 0.01) * ec) * 100.0) <= formulaBase
{
    assert 0.0 <= ec <= 1.0;
    expect 0.0 <= ec <= 1.0;
    if ec == 1.0 {
        result := formulaBase;
    }
    else {
        var base := formulaBase * 0.01;
        var mult := base * ec;
        result := mult * 100.0;
        assert result == formulaBase * ec ==> result <= formulaBase;
        assert result >= 0.0 && result <= formulaBase;
        assert (((formulaBase * 0.01) * ec) * 100.0) <= formulaBase;
        expect result == formulaBase * ec ==> result <= formulaBase;
        expect result >= 0.0 && result <= formulaBase;
        expect (((formulaBase * 0.01) * ec) * 100.0) <= formulaBase;
    }
}

method Total(finding:real, surface:real, env:real) returns (cwss:real)
{
    cwss := finding * surface * env; 
}

