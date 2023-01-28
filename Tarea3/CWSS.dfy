trait FormulaBase {
    const oneHundred := 100 as real;
    const base20 := 20 as real;
    const base15 := 15 as real;
    const base10 := 10 as real;
    const base5 := 5 as real;
    const base4 := 4 as real;
    const base3 := 3 as real;
    const zero := 0 as real;
    const one := 1 as real;

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
}

class BaseFinding extends FormulaBase {
    
    var technicalImpact :real;
    var acquiredProvilege :real;
    var acquiredProvilegeLayer :real;
    var findingConfidence :real;
    var internalControlEffectiveness :real;

    constructor(ti:real, ap: real, al:real, ic:real, fc:real)
        ensures technicalImpact == ti
        ensures acquiredProvilege == ap
        ensures acquiredProvilegeLayer == al
        ensures internalControlEffectiveness == ic
        ensures findingConfidence == fc
    {
        technicalImpact := ti;
        acquiredProvilege := ap;
        acquiredProvilegeLayer := al;
        internalControlEffectiveness := ic;
        findingConfidence := fc;
    }

    /*method funcTechnicalImpact(tecImpact:int) returns (t:int)
        ensures t >= zero && t <= one
        ensures tecImpact == zero ==> t == zero
        ensures tecImpact != zero ==> t == one
    {
        if tecImpact == zero { t:= zero; } else { t:= one; }
    }*/

    method funcBaseFinding() returns (baseFinding:real)
        requires zero <= technicalImpact <= one
    {
        var fti := funcImpact(technicalImpact);
        assert zero <= fti <= one;
        
        baseFinding := ((base10 * technicalImpact + base5 * (acquiredProvilege + acquiredProvilegeLayer) + 
            base5 * findingConfidence) * fti * internalControlEffectiveness) * base4;
    }
}


class AttackSurface extends FormulaBase {

    var requiredPrivilege : real;
    var requiredPrivilegeLayer : real;
    var accessVector : real;
    var authenticationStrenght : real;
    var levelOfInteraction : real;
    var deploymentScope : real;

    constructor (rp:real, rl:real, av:real, asn:real, lin:real, sc:real) 
        ensures requiredPrivilege == rp
        ensures requiredPrivilegeLayer == rl
        ensures accessVector == av
        ensures authenticationStrenght == asn
        ensures levelOfInteraction == lin
        ensures deploymentScope == sc
    { 
        requiredPrivilege := rp;
        requiredPrivilegeLayer := rl;
        accessVector := av;
        authenticationStrenght := asn;
        levelOfInteraction := lin;
        deploymentScope := sc;
    }

    method funcAttackSurface() returns (attackSurface:real)
    {        
        attackSurface := (base20 * (requiredPrivilege + requiredPrivilegeLayer + accessVector)
            + base20 * deploymentScope + base15 * levelOfInteraction + base5 * authenticationStrenght);

        attackSurface := attackSurface / oneHundred;   
        assert zero <= attackSurface <= one ==> (attackSurface / oneHundred) <= one;   
    } 
}

class Environmental extends FormulaBase {
    var businessImpact:real;
    var likelihoodOfDiscovery:real;
    var likelihoodOfExploit:real;
    var prevalence:real;
    var externalControlEffectiveness:real;

    constructor (bi:real, di:real, ex:real, ec:real, p:real) 
        ensures businessImpact == bi
        ensures likelihoodOfDiscovery == di
        ensures likelihoodOfExploit == ex
        ensures externalControlEffectiveness == ec
        ensures prevalence == p
    {
        businessImpact := bi;
        likelihoodOfDiscovery := di;
        likelihoodOfExploit := ex;
        externalControlEffectiveness := ec;
        prevalence := p;
    }

    method funcEnvironmental() returns (environmental:real)
        requires zero <= businessImpact <= one
    {        
        var fbi := funcImpact(businessImpact);
        assert zero <= fbi <= one;
        environmental := ((base10 * businessImpact + base3 * likelihoodOfDiscovery + base4 * likelihoodOfExploit + base3 * prevalence)
            * fbi * externalControlEffectiveness);
        environmental := environmental / base20;
    } 
}

class CWSS extends FormulaBase {

    constructor () { }
    
    method CalculateBaseFinding(ti:real, ap:real, al:real, ic:real, fc:real) returns (baseFinding:real)
        requires zero <= ti <= one
        requires zero <= ap <= one
        requires zero <= al <= one
        requires zero <= ic <= one
        requires zero <= fc <= one
        //ensures zero <= baseFinding <= oneHundred
    {
        var bf := new BaseFinding(ti, ap, al, ic, fc);
        baseFinding := bf.funcBaseFinding();
    }

    method CalculateAttackSurface(rp:real, rl:real, av:real, asn:real, lin:real, sc:real) returns (attackSurface:real) 
        requires zero <= rp <= one
        requires zero <= rl <= one
        requires zero <= av <= one
        requires zero <= asn <= one
        requires zero <= lin <= one
        requires zero <= sc <= one
    {
        var surface := new AttackSurface(rp, rl, av, asn, lin, sc);
        var test := surface.funcAttackSurface();
        //assert zero <= surface <= oneHundred;
    }

    method CalculateEnvironmental(bi:real, di:real, ex:real, ec:real, p:real) returns (environmental:real) 
        requires zero <= bi <= one
        requires zero <= di <= one
        requires zero <= ex <= one
        requires zero <= ec <= one
        requires zero <= p <= one
    {
        var env := new Environmental(bi, di, ex, ec, p);
        environmental := env.funcEnvironmental();
    }    

    method CalculateCWSS() returns (cwss:real) 
        //ensures zero <= cwss <= oneHundred
    {
        var bf := CalculateBaseFinding(1.0,1.0,0.2,1.0,1.0);
        //assert zero <= bf <= oneHundred;
        var asf := CalculateAttackSurface(1.0,1.0,1.0,1.0,1.0,1.0);
        //assert zero <= asf <= one;
        var env :=  CalculateEnvironmental(1.0,1.0,1.0,1.0,1.0);
        //assert zero <= env <= one;
        cwss := (bf*asf*env);
        //assert zero <= cwss <= oneHundred; 
    }
}
