//! Inference alternatives must remain independent when substitutions are shared.
use ferrum_silver::parser::{
    parse_ast::{PTypeSubstitution, p_type_var, type_from_signature},
    parse_ast_keyword::SignatureType,
};

#[test]
fn generalising_one_candidate_preserves_other_candidates() {
    let boolean = type_from_signature(&SignatureType::Bool);
    let impure = type_from_signature(&SignatureType::Impure);
    let original =
        PTypeSubstitution::new([("#T".into(), boolean.clone())].into_iter().collect(), true);
    let alternative = original.clone();
    let widened = alternative.add(&p_type_var("#T"), &impure).unwrap();
    assert!(widened.get("#T").unwrap().structurally_equals(&impure));
    for unchanged in [&original, &alternative] {
        assert!(unchanged.get("#T").unwrap().structurally_equals(&boolean));
    }
    let removed = widened.without("#T");
    assert!(removed.get("#T").is_none());
    assert!(widened.get("#T").unwrap().structurally_equals(&impure));
    assert!(original.get("#T").unwrap().structurally_equals(&boolean));
}

#[test]
fn completing_a_substitution_does_not_bind_another_alternative() {
    let original = PTypeSubstitution::new(
        [("#Result".into(), p_type_var("#Element"))]
            .into_iter()
            .collect(),
        false,
    );
    let int = type_from_signature(&SignatureType::Int);
    let boolean = type_from_signature(&SignatureType::Bool);
    let integers = original.clone().insert("#Element".into(), int.clone());
    let booleans = original.clone().insert("#Element".into(), boolean.clone());
    for (candidate, expected) in [(&integers, &int), (&booleans, &boolean)] {
        assert!(
            candidate
                .get("#Result")
                .unwrap()
                .structurally_equals(expected)
        );
        assert!(
            candidate
                .get("#Element")
                .unwrap()
                .structurally_equals(expected)
        );
        assert!(candidate.is_fully_reduced());
    }
    assert!(original.get("#Element").is_none());
    assert!(
        original
            .get("#Result")
            .unwrap()
            .structurally_equals(&p_type_var("#Element"))
    );
    assert!(integers.compose(&booleans).is_err());
}
