trait FormulaBase {
    const hundred : real := 100.0;
    const ninetyfive : real := 95.0;
    const eigthy : real := 80.0;
    const sixty : real := 60.0;
    const fourty : real := 40.0;
    const twenty : real := 20.0;
    const fifteen : real := 15.0;
    const ten : real := 10.0;
    const five : real := 5.0;
    const four : real := 4.0;
    const three : real := 3.0;
    const zero : real := 0.0;
    const one : real := 1.0;
    const twenty_multiplier : real := 0.05;
    const minimum : real := 0.01;

    method funcImpact(impact:real) returns (result:real)
    requires zero == impact || zero < impact <= one
    requires one == impact || zero <= impact < one
    ensures impact == zero ==> result == zero
    ensures impact != zero ==> result == one
    ensures zero == result || one == result
    {
        assert zero == impact || zero < impact <= one;
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

    method funcBaseFinding() returns (baseFinding:real)
        requires zero <= technicalImpact <= one
        requires zero <= acquiredProvilege <= one
        requires zero <= acquiredProvilegeLayer <= one
        requires zero <= internalControlEffectiveness <= one
        requires zero <= findingConfidence <= one
        ensures zero <= baseFinding <= hundred
    {
        var fti := funcImpact(technicalImpact);
        var formulaBase := ((ten*technicalImpact) + (five*(acquiredProvilege+acquiredProvilegeLayer)) + (five*findingConfidence));
        
        assert zero <= fti <= one;
        if (fti * internalControlEffectiveness == zero) { baseFinding := zero; }
        else if (fti * internalControlEffectiveness == one) { baseFinding := formulaBase * four; }
        else if ( fti == one && zero < internalControlEffectiveness <= one ) { baseFinding := (formulaBase * internalControlEffectiveness) * four; }

        if baseFinding < zero { baseFinding:= zero; } 
        else if baseFinding > hundred { baseFinding := hundred; }
        else { baseFinding := baseFinding; }   
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
        requires zero <= requiredPrivilege <= one
        requires zero <= requiredPrivilegeLayer <= one
        requires zero <= accessVector <= one
        requires zero <= deploymentScope <= one
        requires zero <= levelOfInteraction <= one
        requires zero <= authenticationStrenght <= one
        ensures zero <= attackSurface <= one
    {        
        var accumulator := (twenty*requiredPrivilege);
        assert zero <= accumulator <= twenty;
        accumulator := accumulator + (twenty*requiredPrivilegeLayer);
        assert zero <= accumulator <= fourty;
        accumulator := accumulator + (twenty*accessVector);
        assert zero <= accumulator <= sixty;
        accumulator := accumulator + (twenty*deploymentScope);
        assert zero <= accumulator <= eigthy;
        accumulator := accumulator + (fifteen*levelOfInteraction);
        assert zero <= accumulator <= ninetyfive;
        accumulator := accumulator + (five*authenticationStrenght);  
        assert zero <= accumulator <= hundred;  
        attackSurface := accumulator * minimum; 
        assert zero <= attackSurface <= one;  

        if attackSurface < zero { attackSurface:= zero; assert accumulator == zero; }
        else if attackSurface > one { attackSurface := one; assert accumulator == one; }
        else { attackSurface := attackSurface; assert zero <= attackSurface <= one; }
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
        requires zero <= likelihoodOfDiscovery <= one
        requires zero <= likelihoodOfExploit <= one
        requires zero <= prevalence <= one
        requires zero <= externalControlEffectiveness <= one
        ensures zero <= environmental <= one
    {        
        var fbi := funcImpact(businessImpact);
        assert businessImpact == zero ==> businessImpact == zero;
        assert zero == fbi || one == fbi;
        var formulaBase := (ten*businessImpact) + (three*likelihoodOfDiscovery) + (four*likelihoodOfExploit) + (three*prevalence);
        assert zero <= formulaBase <= twenty;

        environmental := formulaBase;
        if (zero < fbi < one) { environmental := environmental * fbi; }
        if (zero < externalControlEffectiveness < one) { environmental := environmental * externalControlEffectiveness; }
        if (fbi * externalControlEffectiveness == zero) { environmental := zero; }
        else { environmental := environmental * twenty_multiplier; }
        
        if environmental < zero { environmental:= zero; assert environmental == zero; } 
        else if environmental > one { environmental := one; assert environmental == one; }
        else { environmental := environmental; assert zero <= environmental <= one; }   
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
        ensures zero <= baseFinding <= hundred
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
        ensures zero <= attackSurface <= one
    {
        var surface := new AttackSurface(rp, rl, av, asn, lin, sc);
        attackSurface := surface.funcAttackSurface();
    }

    method CalculateEnvironmental(bi:real, di:real, ex:real, ec:real, p:real) returns (environmental:real) 
        requires zero <= bi <= one
        requires zero <= di <= one
        requires zero <= ex <= one
        requires zero <= ec <= one
        requires zero <= p <= one
        ensures zero <= environmental <= one
    {
        var env := new Environmental(bi, di, ex, ec, p);
        environmental := env.funcEnvironmental();
    }    

    method CalculateCWSS(ti:real, ap:real, al:real, ic:real, fc:real, rp:real, rl:real, av:real, asn:real, lin:real, sc:real, bi:real, di:real, ex:real, ec:real, p:real) returns (cwss:real) 
        requires zero <= ti <= one
        requires zero <= ap <= one
        requires zero <= al <= one
        requires zero <= ic <= one
        requires zero <= fc <= one
        requires zero <= rp <= one
        requires zero <= rl <= one
        requires zero <= av <= one
        requires zero <= asn <= one
        requires zero <= lin <= one
        requires zero <= sc <= one
        requires zero <= bi <= one
        requires zero <= di <= one
        requires zero <= ex <= one
        requires zero <= ec <= one
        requires zero <= p <= one
        ensures zero <= cwss <= hundred
    {
        print "\n Base Finding Subscore: ";
        var bf := CalculateBaseFinding(ti, ap, al, ic, fc);
        assert zero <= bf <= hundred;

        print "\n Attack Surface Subscore: ";
        var asf := CalculateAttackSurface(rp, rl, av, asn, lin, sc);
        assert zero <= asf <= one;

        print "\n Environmental Subscore: ";
        var env :=  CalculateEnvironmental(bi, di, ex, ec, p);
        assert zero <= env <= one;

        print "\n Resultado del CWSS: ";
        cwss := bf * asf * env;
        if cwss < zero { cwss := zero; } else if cwss > hundred { cwss := hundred; } 
        else { cwss := cwss; }        
        assert zero <= cwss <= hundred; 
        print "\n";
        print "\n =====================================================================";
    }
}




