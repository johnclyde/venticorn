use venticorn::acorn_type::Typeclass;
use venticorn::constant_name::LocalConstantName;

#[test]
fn simple_chains_expose_syntax_without_reparsing_display_names() {
    let plain = LocalConstantName::unqualified("value");
    assert_eq!(plain.name_chain(), Some(vec!["value"]));
    let attribute = LocalConstantName::attribute("State", "flag");
    assert_eq!(attribute.name_chain(), Some(vec!["State", "flag"]));
    for invalid in [
        LocalConstantName::unqualified("State.Marked.flag"),
        LocalConstantName::attribute("State.Marked", "flag"),
        LocalConstantName::attribute("State", "Marked.flag"),
    ] {
        assert!(invalid.name_chain().is_none());
    }
    let instance = LocalConstantName::instance(
        &Typeclass {
            module_id: 11,
            name: "Marked".into(),
        },
        "flag",
        "State",
    );
    assert!(instance.name_chain().is_none());
}
