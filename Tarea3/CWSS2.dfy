

const hundred := 100.0 as real;
const twenty := 20.0 as real;
const fifteen := 15.0 as real;
const ten := 10.0 as real;
const five := 5.0 as real;
const four := 4.0 as real;
const three := 3.0 as real;
const zero := 0.0 as real;
const one := 1.0 as real;
const minimum := 0.01 as real;


method funcImpact(impact:real) returns (result:real)
    requires zero <= impact && impact <= one
    ensures impact == zero ==> result == zero
    ensures impact != zero ==> result == one
    ensures result >= zero && result <= one
{
    assert zero <= impact && impact <= one;
    if impact == zero { result:= zero; } else { result:= one; }
    assert impact == zero ==> result == zero;
    assert impact != zero ==> result == one;
}

// AFTER THIS POINT MAIN METHOD AND FUNCTIONS AS WELL

method Main() {

    var baseFindig := funcBaseFinding(0.9, 1.0, 1.0, 1.0, 1.0);
    print baseFindig;
    print "\n";
    var attackSurface := funcAttackSurface(0.9, 1.0, 1.0, 1.0, 0.9, 1.0);
    print attackSurface;
    print "\n";
    var environmental := funcEnvironmental(1.0, 1.0, 1.0, 1.0, 1.0);
    print environmental;
    print "\n";

    var base : real := baseFindig * attackSurface * environmental;
    print base;
}

method funcBaseFinding(ti:real, ap:real, al:real, ic:real, fc:real) returns (baseFinding:real)
    requires zero <= ti <= one
    requires zero <= ap <= one
    requires zero <= al <= one
    requires zero <= ic <= one
    requires zero <= fc <= one
    ensures zero <= baseFinding <= hundred
{
    var fti := funcImpact(ti);
    assert zero <= fti <= one;
    
    var block1 := (ten * ti);
    var block2 := (five * (ap + al));
    var block3 := (five * fc);
    var block4 := (block1 + block2);
    var block5 := (block4 + block3);
    var block6 := (block5 * fti);
    var block7 := (block6 * ic);
    baseFinding := block5 * four;

    assert zero <= block1 <= hundred;
    assert zero <= block2 <= hundred;
    assert zero <= block3 <= hundred;
    assert zero <= block4 <= hundred;
    assert zero <= block5 <= hundred;
    assert zero <= block6 <= hundred;
    assert zero <= baseFinding <= hundred;
}

method funcAttackSurface(rp:real, rl:real, av:real, asn:real, lin:real, sc:real) returns (attackSurface:real) 
    requires zero <= rp <= one
    requires zero <= rl <= one
    requires zero <= av <= one
    requires zero <= asn <= one
    requires zero <= lin <= one
    requires zero <= sc <= one
    ensures zero <= attackSurface <= one
{
    var block1 := (rp + rl + av);
    var block2 := (twenty * block1);
    var block3 := (twenty * sc);
    var block4 := (fifteen * lin);
    var block5 := (five * asn);
    var block6 := (block2 + block3);
    var block7 := (block6 + block4);
    var block8 := (block7 + block5);
    attackSurface := (block8 / hundred);
    assert zero <= attackSurface <= one ==> (attackSurface / hundred) <= one;   
} 

method funcEnvironmental(bi:real, di:real, ex:real, ec:real, p:real) returns (environmental:real) 
    requires bi >= zero && bi <= one
    requires di >= zero && di <= one
    requires ex >= zero && ex <= one
    requires zero <= ec <= one
    requires zero <= p <= one
    ensures zero <= environmental <= one
{
    var fbi := funcImpact(bi);
    assert zero <= fbi <= one;
/*
    assert (ten * bi) <= ten;
    assert (three * di) <= ten;
    assert (four * ex) <= four;
    assert (three * p) <= three;
    assert zero <= ((ten * bi) + (three * di) + (four * ex) + (three * p)) <= twenty;
    assert zero <= (((ten * bi) + (three * di) + (four * ex) + (three * p)) * fbi) <= twenty;
    //assert zero <= ((ten * bi) + (three * di) + (four * ex) + (three * p) * fbi) * ec <= twenty;
    //assert zero <= ((ten * bi) + (three * di) + (four * ex) + (three * p) * fbi * ec) * 0.05 <= one;
    environmental:= bi*ten + di*three + ex*four + p*three * fbi * ec * 0.05;
    assert environmental <= twenty;*/

    var block1 := (ten * bi);
    var block2 := (three * di);
    var block3 := (four * ex);
    var block4 := (three * p);

    var block5 := (block1 + block2 + block3 + block4);
    var block6 := (block5 * fbi);
    var block7 := (block6 * ec);
            
    environmental := block6 *0.05;

    assert zero <= block1 <= ten;
    assert zero <= block2 <= three;
    assert zero <= block3 <= four;
    assert zero <= block4 <= three;
    assert zero == block6 || (block6 * fbi) == block6;
    assert block5 == zero || block5 == block5;
    assert zero <= environmental <= one;
    assert zero <= environmental && environmental <= one;
} 

method funcTotal(finding:real, surface:real, env:real) returns (cwss:real)
    requires one <= finding <= hundred;
    requires one <= surface <= one;
    requires one <= env <= one;
    ensures one <= cwss <= hundred;
{
    cwss := surface * hundred;
    assert zero <= cwss <= hundred;
    cwss := (cwss * finding) * minimum;
    assert zero <= cwss <= hundred;
    cwss := cwss * env;
    assert zero <= cwss <= hundred;

    print cwss;
}


