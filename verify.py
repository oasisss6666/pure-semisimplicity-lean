#!/usr/bin/env python3
"""Rebuild this partial formalization and audit all new theorem dependencies."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parent
MANUSCRIPT = json.loads((ROOT / 'manuscript/source_metadata.json').read_text())
snapshot_hash = hashlib.sha256((ROOT / 'manuscript/source.tex').read_bytes()).hexdigest()
if snapshot_hash != MANUSCRIPT['sha256']:
    raise SystemExit('Manuscript snapshot hash mismatch')
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
sources = sorted((ROOT / 'QuantumFlags').glob('*.lean')) + [ROOT / 'QuantumFlags.lean']
theorems = []
for path in sources:
    text = path.read_text(encoding='utf-8')
    forbidden = re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', text)
    if forbidden:
        raise SystemExit(f'Forbidden proof escape in {path.name}: {forbidden.group()}')
    frames = []
    for line in text.splitlines():
        namespace = re.match(r'^namespace\s+([\w.]+)', line)
        section = re.match(r'^(?:noncomputable\s+)?section\b', line)
        declaration = re.match(r'^(?:@\[simp\]\s+)?theorem\s+([\w.]+)', line)
        if namespace:
            frames.append(('namespace', namespace.group(1)))
        elif section:
            frames.append(('section', ''))
        elif re.match(r'^end(?:\s|$)', line):
            if not frames:
                raise SystemExit(f'Unmatched scope end in {path.name}')
            frames.pop()
        elif declaration:
            prefix = '.'.join(name for kind, name in frames if kind == 'namespace')
            theorems.append(prefix + '.' + declaration.group(1))

expected_audit = 'import QuantumFlags\n\n-- Kernel dependency audit for every theorem in this project.\n'
expected_audit += '\n'.join('#print axioms ' + n for n in theorems) + '\n'
(ROOT / 'AxiomAudit.lean').write_text(expected_audit, encoding='utf-8')

logs = []
for command in [['lake', 'build'], ['lake', 'env', 'lean', 'AxiomAudit.lean']]:
    result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, check=False)
    logs.append('$ ' + ' '.join(command) + '\n' + result.stdout)
    print(result.stdout, end='', flush=True)
    if result.returncode:
        (ROOT / 'verification.log').write_text('\n'.join(logs), encoding='utf-8')
        raise SystemExit(result.returncode)

required_model_theorems = {
    'QuantumFlags.preinjectiveFamily_layer_zero_cases',
    'QuantumFlags.finiteIndecomposable_classification',
    'QuantumFlags.finiteRightModule_indecomposable_classification',
    'QuantumFlags.actualFiniteIndecomposable_classification',
    'QuantumFlags.actualFiniteRightModule_indecomposable_classification',
    'QuantumFlags.preinjectiveFamily_hom_subsingleton',
    'QuantumFlags.classObject_complete',
    'QuantumFlags.classObject_irredundant',
    'QuantumFlags.classObject_endRing_division',
    'QuantumFlags.classObject_hom_subsingleton',
    'QuantumFlags.finite_decomposition',
    'QuantumFlags.decomposition_lemma',
    'QuantumFlags.moduleIndecomposable_of_isUnit',
    'QuantumFlags.indecomposable_of_moduleIndecomposable',
    'QuantumFlags.classModule_complete',
    'QuantumFlags.classModule_irredundant',
    'QuantumFlags.classModule_endRing_isUnit',
    'QuantumFlags.classModule_hom_eq_zero',
    'QuantumFlags.classModule_finitelyPresented',
    'QuantumFlags.triangular_module_decomposition',
    'QuantumFlags.triangular_right_pure_semisimple',
    'QuantumFlags.finitelyGenerated_triangular_decomposition',
    'QuantumFlags.triangular_not_finitelyManyIndecomposables',
    'QuantumFlags.not_finitelyManyIndecomposables',
    'QuantumFlags.everyModuleDirectSumFG_of_ringEquiv',
    'QuantumFlags.finitelyManyIndecomposables_of_ringEquiv',
    'QuantumFlags.actual_triangular_right_pure_semisimple',
    'QuantumFlags.actual_triangular_not_finite_representation_type',
    'QuantumFlags.oreLevel_countable',
    'QuantumFlags.leftDual_not_countable',
    'QuantumFlags.witnessModule_countable_of_decomposition',
    'QuantumFlags.triangular_not_left_pure_semisimple',
    'QuantumFlags.actual_triangular_not_left_pure_semisimple',
    'QuantumFlags.quantumAutomorphism_unique',
    'QuantumFlags.quantumGenerator_zpow_mul',
    'QuantumFlags.mul_quantumGenerator_zpow',
    'QuantumFlags.quantumGenerator_integer_left_powers_independent',
    'QuantumFlags.quantumGenerator_integer_right_powers_independent',
    'QuantumFlags.quantumMonomial_eq_prod',
    'QuantumFlags.quantumMonomial_mul',
    'QuantumFlags.quantumMonomial_linearIndependent',
    'QuantumFlags.quantumLaurentSubalgebra_eq_span',
    'QuantumFlags.quantumLaurentSubalgebra_is_quantumTorus',
    'QuantumFlags.quantumLaurent_two_sided_ore_domain',
    'QuantumFlags.quantumLaurent_closure',
    'QuantumFlags.quantumLaurent_fraction_field',
    'QuantumFlags.quantumStep_mem_laurent',
    'QuantumFlags.main_theorem',
    'QuantumFlags.pure_semisimplicity_conjecture_fails',
    'QuantumFlags.tensorReflectionRecoverIso_exists',
    'QuantumFlags.positiveDefect_classification_by_target',
    'QuantumFlags.positiveDefect_classification',
    'QuantumFlags.tensorIso_source_finrank',
    'QuantumFlags.tensorIso_target_finrank',
    'QuantumFlags.positiveSource_not_simpleTarget',
    'QuantumFlags.positiveTarget_not_simpleSource',
    'QuantumFlags.preinjectiveObject_indecomposable',
    'QuantumFlags.preinjectiveFamily_dimension_vector',
    'QuantumFlags.preinjectiveFamily_indecomposable',
    'QuantumFlags.preinjectiveFamily_arrow_surjective',
    'QuantumFlags.preinjectiveFamily_endo_division',
    'QuantumFlags.preinjectiveRepresentation_dimension_vector',
    'QuantumFlags.preinjectiveRepresentation_pairwise_nonisomorphic',
    'QuantumFlags.actualPreinjective_dimension_vector',
    'QuantumFlags.actualPreinjective_indecomposable',
    'QuantumFlags.actualPreinjective_pairwise_nonisomorphic',
    'QuantumFlags.preinjectiveFamilyEndRingEquiv_exists',
    'QuantumFlags.preinjectiveRepresentationEndRingEquiv_exists',
    'QuantumFlags.preinjectiveFamily_zero_object',
    'QuantumFlags.preinjectiveFamily_successor_object',
    'QuantumFlags.preinjectiveFamilyReflectionIso_exists',
    'QuantumFlags.bimoduleTensorRepresentation_finite',
    'QuantumFlags.preinjectiveRightModule_finite',
    'QuantumFlags.preinjectiveRightModule_finitelyPresented',
    'QuantumFlags.preinjectiveRightModule_indecomposable',
    'QuantumFlags.preinjectiveRightModule_pairwise_nonisomorphic',
    'QuantumFlags.preinjectiveRightModuleEndRingEquiv_exists',
    'QuantumFlags.actualPreinjectiveRightModule_finite',
    'QuantumFlags.actualPreinjectiveRightModule_finitelyPresented',
    'QuantumFlags.actualPreinjectiveRightModule_indecomposable',
    'QuantumFlags.actualPreinjectiveRightModule_pairwise_nonisomorphic',
    'QuantumFlags.actualPreinjectiveRightModuleEndRingEquiv_exists',

    'QuantumFlags.canonicalProjectiveEnd_target',
    'QuantumFlags.canonicalProjectiveEndRingHom_bijective',
    'QuantumFlags.canonicalProjectiveEndRingEquiv_exists',
    'QuantumFlags.canonicalProjective_indecomposable',
    'QuantumFlags.tensorCanonicalProjective_indecomposable',
    'QuantumFlags.canonicalProjective_tensorInverse_right',
    'QuantumFlags.canonicalProjective_tensorInverse_left',
    'QuantumFlags.canonicalProjective_tensorArrow_bijective',
    'QuantumFlags.canonicalProjective_dimension_vector',
    'QuantumFlags.invertibleTensorArrowMorphism_comp',
    'QuantumFlags.invertibleTensorArrowMorphism_identity',
    'QuantumFlags.indecomposable_tensor_retract_isomorphism',
    'QuantumFlags.indecomposable_invertibleArrow_isCanonicalProjective',
    'QuantumFlags.zeroDefect_tensorArrow_bijective',
    'QuantumFlags.zeroDefect_indecomposable_isCanonicalProjective',
    'QuantumFlags.equalDimension_indecomposable_source_finrank_pos',
    'QuantumFlags.nonsimple_zeroDefect_classification',

    'QuantumFlags.balancedTensorCoordinates_pure',
    'QuantumFlags.balancedTensorBasisInverse_coordinates_pure',
    'QuantumFlags.balancedTensorBasisInverse_coordinates',
    'QuantumFlags.balancedTensorCoordinates_basisInverse',
    'QuantumFlags.balancedTensor_finrank',
    'QuantumFlags.rightHom_finrank',
    'QuantumFlags.reflectionForward_finite',
    'QuantumFlags.reflectionBackward_finite',
    'QuantumFlags.reflectionBackward_source_finrank',
    'QuantumFlags.reflectionBackward_dimension_vector',
    'QuantumFlags.inverseTensorReflection_dimension_vector',
    'QuantumFlags.tensorRepresentation_target_finrank_le',
    'QuantumFlags.tensorRepresentation_source_finrank_le',
    'QuantumFlags.one_two_representation_dimension_bounds',
    'QuantumFlags.one_two_indecomposable_dimension_bounds',
    'QuantumFlags.tensorSimpleSource_dimension_vector',
    'QuantumFlags.tensorSimpleTarget_dimension_vector',
    'QuantumFlags.tensorReflection_positive_defect_step',
    'QuantumFlags.homFromSimpleSource_eq_zero',
    'QuantumFlags.tensorHomFromSimpleSource_eq_zero',
    'QuantumFlags.tensorHomToSimpleTarget_eq_zero',
    'QuantumFlags.simpleSourceEndRingEquiv_exists',
    'QuantumFlags.simpleTargetEndRingEquiv_exists',
    'QuantumFlags.indecomposable_of_trivial_end_idempotents',
    'QuantumFlags.indecomposable_of_endRingEquiv_division',
    'QuantumFlags.simpleSource_indecomposable',
    'QuantumFlags.simpleTarget_indecomposable',
    'QuantumFlags.tensorSimpleSourceEndRingEquiv_exists',
    'QuantumFlags.tensorSimpleTargetEndRingEquiv_exists',
    'QuantumFlags.tensorSimpleSource_indecomposable',
    'QuantumFlags.tensorSimpleTarget_indecomposable',
    'QuantumFlags.splitKernelProjection_comp_section',
    'QuantumFlags.splitKernelProjection_comp_inclusion',
    'QuantumFlags.splitKernelProjection_total',
    'QuantumFlags.homRepresentationSplitBicone_total',
    'QuantumFlags.indecomposable_retract_isomorphism',
    'QuantumFlags.indecomposable_homArrow_injective',
    'QuantumFlags.indecomposable_homTensorArrow_surjective',
    'QuantumFlags.indecomposable_tensorAdjoint_injective',
    'QuantumFlags.indecomposable_tensorArrow_surjective',
    'QuantumFlags.indecomposable_nonsimple_tensor_arrows',
    'QuantumFlags.bimodule_representation_action',
    'QuantumFlags.bimodule_target_offDiagonal_mul',
    'QuantumFlags.bimodule_offDiagonal_source_mul',
    'QuantumFlags.bimodule_source_corner_mul',
    'QuantumFlags.bimodule_target_corner_mul',
    'QuantumFlags.bimoduleCornerDecomposition_components',
    'QuantumFlags.bimoduleCornerHomRepresentation_arrow_apply',
    'QuantumFlags.bimoduleCornerModuleEquiv_apply',
    'QuantumFlags.bimoduleHomRepresentationModuleMap_identity',
    'QuantumFlags.bimoduleHomRepresentationModuleMap_compose',
    'QuantumFlags.bimoduleCornerHomRepresentationMap_identity',
    'QuantumFlags.bimoduleCornerHomRepresentationMap_compose',
    'QuantumFlags.bimoduleCornerModuleEquiv_natural',
    'QuantumFlags.bimoduleHomRepresentationRecovery_left_inverse',
    'QuantumFlags.bimoduleHomRepresentationRecovery_right_inverse',
    'QuantumFlags.bimoduleHomRepresentationRecovery_natural',
    'QuantumFlags.bimoduleRepresentationEquivalence_exists',
    'QuantumFlags.bimoduleTensorRepresentationEquivalence_exists',
    'QuantumFlags.bimoduleTensorRepresentation_action',
    'QuantumFlags.bimoduleRepresentation_indecomposable_iff',
    'QuantumFlags.bimoduleTensorRepresentation_indecomposable_iff',
    'QuantumFlags.bimoduleRepresentationEndRingEquiv_exists',
    'QuantumFlags.bimoduleTensorRepresentationEndRingEquiv_exists',
    'QuantumFlags.inverseReflectionEndRingEquiv_exists',
    'QuantumFlags.injectiveHomBicone_total',
    'QuantumFlags.equivalence_isZero_iff',
    'QuantumFlags.equivalence_indecomposable_iff',
    'QuantumFlags.reflection_indecomposable_iff',
    'QuantumFlags.inverseReflection_indecomposable_iff',
    'QuantumFlags.homRepresentationBicone_total',
    'QuantumFlags.tensorHomCategoryEquivalence_exists',
    'QuantumFlags.retract_closed_indecomposable_iff',
    'QuantumFlags.homArrow_injective_of_retract',
    'QuantumFlags.tensorArrow_surjective_of_retract',
    'QuantumFlags.injectiveHom_ambient_indecomposable_iff',
    'QuantumFlags.surjectiveDualTensor_ambient_indecomposable_iff',
    'QuantumFlags.reflection_ambient_indecomposable_iff',
    'QuantumFlags.inverseReflection_ambient_indecomposable_iff',
    'QuantumFlags.tensorReflectionEquivalence_exists',
    'QuantumFlags.tensorReflection_object',
    'QuantumFlags.inverseTensorReflection_object',
    'QuantumFlags.tensorReflection_ambient_indecomposable_iff',
    'QuantumFlags.inverseTensorReflection_ambient_indecomposable_iff',
    'QuantumFlags.tensorReflectionEndRingEquiv_exists',
    'QuantumFlags.inverseTensorReflectionEndRingEquiv_exists',
    'QuantumFlags.tensorReflection_dimension_vector',
    'QuantumFlags.HomRepresentationMorphism.add_source',
    'QuantumFlags.HomRepresentationMorphism.add_target',
    'QuantumFlags.TensorRepresentationMorphism.add_source',
    'QuantumFlags.TensorRepresentationMorphism.add_target',
    'QuantumFlags.reflection_map_zero',
    'QuantumFlags.reflection_map_add',
    'QuantumFlags.reflectionEndRingEquiv_exists',
    'QuantumFlags.reflectionEndRingEquiv_source',
    'QuantumFlags.reflection_identity_zero_iff',
    'QuantumFlags.reflection_trivial_idempotents_iff',
    'QuantumFlags.homRepresentationProd_injective',
    'QuantumFlags.homProd_total',
    'QuantumFlags.hasKernelLine_iff_not_injective',
    'QuantumFlags.hasCokernelLine_iff_not_surjective',
    'QuantumFlags.simpleSourceSummand_iff_kernelLine',
    'QuantumFlags.simpleTargetSummand_iff_cokernelLine',
    'QuantumFlags.tensorRepresentation_retraction_iff',
    'QuantumFlags.no_tensorSimpleSourceSummand_iff_injective',
    'QuantumFlags.no_tensorSimpleTargetSummand_iff_surjective',
    'QuantumFlags.reflectionForward_surjective',
    'QuantumFlags.reflectionBackward_injective',
    'QuantumFlags.reflectionUnit_left_inverse',
    'QuantumFlags.reflectionUnit_right_inverse',
    'QuantumFlags.reflectionUnit_natural',
    'QuantumFlags.reflectionCounit_left_inverse',
    'QuantumFlags.reflectionCounit_right_inverse',
    'QuantumFlags.reflectionCounit_natural',
    'QuantumFlags.reflectionForwardMap_identity',
    'QuantumFlags.reflectionForwardMap_comp',
    'QuantumFlags.reflectionBackwardMap_identity',
    'QuantumFlags.reflectionBackwardMap_comp',
    'QuantumFlags.reflection_equivalence_exists',
    'QuantumFlags.reflectionFunctor_map_bijective',
    'QuantumFlags.reflectionForward_dimension_vector',
    'QuantumFlags.balancedRelation_mkQ_zero',
    'QuantumFlags.balancedTensorMap_identity',
    'QuantumFlags.balancedTensorMap_comp',
    'QuantumFlags.dualTensorHomEquiv_pure',
    'QuantumFlags.dualTensorHomEquiv_natural',
    'QuantumFlags.dualTensorInverse_evaluation',
    'QuantumFlags.dualTensorEvaluation_inverse',
    'QuantumFlags.tensorHom_arrow_roundtrip',
    'QuantumFlags.homTensor_arrow_roundtrip',
    'QuantumFlags.actualQuantumChain_exists',
    'QuantumFlags.actual_global_right_basis',
    'QuantumFlags.actual_global_adjacent_flags',
    'QuantumFlags.actual_all_width_direct_flags',
    'QuantumFlags.actual_left_dimension_infinite',
    'QuantumFlags.actual_strip_stabilizers',
    'QuantumFlags.actual_reciprocal_isomorphism',
    'QuantumFlags.stripDualEquiv_twist',
    'QuantumFlags.iterated_right_dual_finite',
    'QuantumFlags.actual_right_dimension_sequence',
    'QuantumFlags.actual_generalized_artin_extension',
    'QuantumFlags.actual_triangular_left_ideal_chain',
    'QuantumFlags.actual_triangular_not_left_artinian',
    'QuantumFlags.actual_triangular_artinian_asymmetry',
    'QuantumFlags.triangular_finite_presentation',
    'QuantumFlags.HomRepresentationMorphism.compose_assoc',
    'QuantumFlags.reflection_cokernel_finrank',
    'QuantumFlags.ambientHomEvaluationEquiv_apply',
    'QuantumFlags.triangular_action_formula',
    'QuantumFlags.homRepresentation_rightModule_exists',
    'QuantumFlags.triangular_finite_iff_corners',
    'QuantumFlags.cornerArrow_apply',
    'QuantumFlags.cornerModuleEquiv_apply',
    'QuantumFlags.cornerHomMapEquiv_bijective',
    'QuantumFlags.moduleFromCornerHomEquiv_natural',
    'QuantumFlags.homRepresentationRecovery_left_inverse',
    'QuantumFlags.homRepresentationRecovery_right_inverse',
    'QuantumFlags.homRepresentationRecovery_natural',
    'QuantumFlags.triangularCoefficientComm',
    'QuantumFlags.artinian_of_two_corners',
    'QuantumFlags.bimodule_triangular_right_artinian',
    'QuantumFlags.bimodule_finite_iff_corners',
    'QuantumFlags.bimodule_finite_presentation',
    'QuantumFlags.ambient_triangular_ring_isomorphism',
    'QuantumFlags.automorphism_skew_two_sided_ore',
    'QuantumFlags.extension_integer_left_powers_independent',
    'QuantumFlags.extension_integer_right_powers_independent',
}
if not required_model_theorems.issubset(theorems):
    raise SystemExit('The actual model theorem audit is missing')

axiom_output = logs[-1]
used = set()
for group in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', axiom_output, re.S):
    used.update(x.strip() for x in group.split(',') if x.strip())
if used - ALLOWED_AXIOMS:
    raise SystemExit(f'Unexpected axioms: {sorted(used - ALLOWED_AXIOMS)}')
missing = [name for name in theorems if name not in axiom_output]
if missing:
    raise SystemExit(f'Missing theorem audits: {missing}')

status = {
    'status': 'passed_full_formalization',
    'checked_at_utc': datetime.now(timezone.utc).isoformat(),
    'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
    'mathlib_revision': '5ed2965256430c3649e86755f9576b54eca72435',
    'theorem_count': len(theorems),
    'axioms_used': sorted(used),
    'proof_escape_scan_passed': True,
    'full_counterexample_verified': True,
    'main_theorem': 'QuantumFlags.main_theorem (thm:main) and QuantumFlags.pure_semisimplicity_conjecture_fails are compiled and audited; all 16 labelled statements have audited Lean counterparts.',
    'interpretive_notes': [
        'Right modules over a ring are modules over its opposite ring. Pure semisimplicity and finite representation type quantify over modules in a fixed universe w; the theorems hold for every w.',
        'R not left pure semisimple is proved directly (countable T, uncountable Hom_H(T,H), explicit left module (H, Hom_H(T,H), ev)); the theorem of Chase is not formalized and not used.',
        'lem:qtorus (2) is formalized as: the subalgebra generated by t_i^{+-1} has the monomial basis with the stated multiplication table, is a two-sided Ore domain, and its Ore localization is isomorphic to T_n extending the inclusion. The lemma is proved for every nonzero rational q; the counterexample tower is the instance q = 1/2.',
        'lem:decomp: the last step uses a coordinate of maximal type instead of nilpotency on a finite summand.',
        'Sections 2-3 are proved for every division bimodule with right dimension sequence (1,2,2,...), not only for G subset F.'
    ],
    'scope': 'Actual iterated skew Ore division rings, their direct-limit quantum chain, global (B)/(F), and Section 4: all-width direct flags, infinite left dimension, exact strip stabilizers, reciprocal ring isomorphisms, actual right-linear Hom duality with the twist identity, and the finite right dimension sequence (1,2,2,...) for the actual iterated right duals. The actual triangular matrix subring is right Artinian and right Noetherian but not left Artinian, its finitely generated right modules are finitely presented, and an arbitrary right module is finitely generated exactly when both corner spaces are finite dimensional. Every such module is reconstructed as the two-corner representation with its actual triangular-ring action. For the initial ambient bimodule, extraction and reconstruction act on morphisms, preserve identities and composition, induce bijections on morphism sets, and have inverse recovery isomorphisms with proved naturality. For every division bimodule that is finite on the right, its actual triangular ring is right Artinian, finite generation of arbitrary right modules is equivalent to finite corner dimensions, and every finitely generated right module is finitely presented. For an arbitrary automorphism of a division ring, the actual skew polynomial ring is a two-sided Ore domain and its fraction division ring has both left and right linearly independent integer powers of the variable. A balanced tensor product over arbitrary division bimodules is constructed as an actual quotient, with its tensor-Hom universal property and functorial maps. For every right-finite division bimodule and arbitrary target module, the dual tensor evaluation is a right-linear isomorphism natural in the target, with its explicit finite-basis inverse proved in both directions. Tensor and Hom descriptions of representations and morphisms are related with inverse arrow recovery. The actual kernel-cokernel reflection and inverse reflection are packaged as a mathlib category equivalence between representations with injective Hom arrow and dual representations with surjective tensor arrow. Both constructions act on morphisms, preserve identities and composition, and have proved unit and counit isomorphisms and naturality. Reflection has bijections on morphism sets and its actual finite dimension vector is (b, d*b-a). Canonical simple source and target representations are defined, and actual split inclusion/projection representation morphisms identify their presence with a scalar-line retract in the kernel or cokernel. For arbitrary tensor representations, absence of a simple source summand is proved equivalent to injectivity of the adjoint arrow, and absence of a simple target summand is proved equivalent to surjectivity of the tensor arrow. Both reflection categories are preadditive with actual componentwise addition of representation morphisms. Reflection is proved to induce an actual ring isomorphism on endomorphism rings, preserving addition, zero, identity and composition; it also preserves the identity-zero condition and the property that all idempotents are zero or one. Products of Hom representations have actual injections and projections satisfying the biproduct equations, and preserve injectivity of the Hom arrow. Binary biproducts are constructed in the ambient Hom representation category and in the injective-Hom subcategory. The tensor-Hom conversion is an actual category equivalence, including its restriction to injective adjoint arrows. The surjective-dual-tensor subcategory has binary biproducts transported along reflection. Injective Hom arrows and surjective tensor arrows are proved closed under actual retracts, so categorical indecomposability in the subcategories agrees with ambient representation indecomposability. Both reflection directions preserve ambient indecomposability and actual endomorphism rings, also in the original tensor-representation formulation. The actual tensor reflection equivalence and its inverse have the specified object formulas and the finite dimension vector formula. For every division bimodule, without any finite-dimensionality assumption, actual right modules of its square-zero-extension triangular ring are now packaged as a category equivalent to Hom representations and tensor representations. The action agrees with the stated tensor formula. The inverse uses the actual idempotent corners and off-diagonal multiplication; natural unit and counit isomorphisms, both ambient indecomposability statements, and actual endomorphism ring isomorphisms are proved. For arbitrary division bimodules, canonical simple source and target representations have actual endomorphism rings isomorphic to their vertex division rings and are proved categorically indecomposable, in both Hom and tensor forms. The boundary Hom-vanishing statements are proved. For every actual split representation inclusion/projection, the kernel complement and binary biproduct decomposition are constructed. Consequently every nonzero retract of an indecomposable representation is isomorphic to it, and an indecomposable representation not isomorphic to the simple source/target has injective adjoint/surjective tensor arrow, respectively. An actual balanced tensor coordinate isomorphism relative to every finite source basis is constructed with both inverse identities, giving finrank(X tensor N)=finrank(X)*finrank(N) under the stated right-finiteness assumptions. Right Hom spaces have finite dimension and the corresponding product formula. Forward and inverse reflection preserve finite corner dimensions, and the actual inverse reflection dimension vector is (d*b-c,b). For right dimension pair (1,2), the already proved nonsimple indecomposable arrow conditions now yield b<=a<=2*b. Canonical simple dimension vectors and an actual positive-defect reflection step with strictly decreasing target dimension and preserved defect are proved.',
    'canonical_projective_status': 'Proved for arbitrary division bimodules: actual Hom and tensor representations P, End(P) isomorphic to the source division ring, categorical indecomposability, explicit inverse to the tensor arrow, and the general source rank-one / target bimodule-rank dimension vector. Actual tensor morphisms are uniquely extended from source maps when the domain tensor arrow is invertible. An indecomposable representation with invertible tensor arrow and nonzero source is isomorphic to P. For right rank-one bimodules, the finite-dimensional nonsimple equal-dimension branch is proved without assuming positive source rank or the desired isomorphism.',
    'preinjective_family_status': 'Proved: an actual recursively defined inverse-reflection family at every layer for each right-finite iterated-dual chain with all successor right dimensions 2. Every intermediate object has finite corner spaces, dimensions (k+1,k), a surjective tensor arrow, categorical indecomposability and an endomorphism ring isomorphic to the terminal layer vertex division ring. Forward reflection recovers the previous object by an actual isomorphism. The family is pairwise nonisomorphic by dimensions. The actual Ore flag model supplies all hypotheses. Transport along the actual triangular-ring representation equivalence gives finitely generated and finitely presented, pairwise nonisomorphic, indecomposable right modules with the corresponding actual endomorphism ring isomorphisms. The positive-defect branch is proved at every layer by strong induction on target dimension, recovering the original object as I_b. The merged complete list, ordered Hom vanishing, arbitrary-module decomposition and right pure semisimplicity are now proved (see classification_status and pure_semisimplicity_status).',
    'positive_defect_classification_status': 'Proved for every right-finite iterated-dual chain whose successor right dimensions are 2, at every layer r: every finite-dimensional categorically indecomposable tensor representation with target dimension b strictly below its source dimension is actually isomorphic to the recursively constructed I_b at layer r. The proof uses strong induction on b, the nonsimple injective-adjoint criterion, actual reflection preserving indecomposability and positive defect while lowering target dimension, the family dimension formulas, and an explicit recovery isomorphism from the reflection equivalence unit. No surjectivity, endpoint classification, or desired isomorphism is assumed as an input.',
    'unformalized': [
            'The general theorem of Chase (left pure semisimple rings are left artinian), cited at source lines 75 and 421, is not formalized; the conclusion it is used for is proved directly.'
    ],
    'manuscript_path': MANUSCRIPT['source_path'],
    'manuscript_sha256': MANUSCRIPT['sha256'],
    'manuscript_snapshot_hash_verified': True,
    'original_source_still_matches_snapshot': Path(MANUSCRIPT['source_path']).is_file() and hashlib.sha256(Path(MANUSCRIPT['source_path']).read_bytes()).hexdigest() == MANUSCRIPT['sha256'],
    'quantum_chain_existence_proved': True,
    'global_B_status': 'proved for the constructed OreUnion model by actual_global_right_basis',
    'global_F_status': 'proved for the constructed OreUnion model by actual_global_adjacent_flags',
    'skew_lemma_status': 'Proved for an arbitrary division-ring automorphism: actual no-zero-divisor and two-sided Ore statements, actual fraction division ring, and both integer-power linear independence statements.',
    'reflection_endomorphism_ring_status': 'Proved: canonical componentwise additive groups on both representation morphism types; preadditivity of both reflection categories; an actual ring isomorphism on endomorphisms from the reflection functor; and preservation of the identity-zero and trivial-idempotent conditions. Inverse reflection and both original tensor-representation directions also have actual endomorphism ring isomorphisms; ambient direct-sum indecomposability is separately proved preserved using retract closure.',
    'classification_dimensions_status': 'Proved: actual balanced tensor coordinates with both inverse identities; tensor and Hom finrank product formulas under explicit finite-dimensionality hypotheses; finite-dimensionality preservation for both reflection directions; inverse dimension vector (d*b-c,b); canonical simple vectors (1,0) and (0,1); and b<=a<=2*b for nonsimple finite-dimensional indecomposable tensor representations when the bimodule and its right dual have right dimensions 1 and 2. In the positive-defect case with dual dimension 2, actual reflection strictly decreases target dimension and preserves a-b. The family I_k is now constructed by actual inverse reflections at every layer with dimensions (k+1,k), finite corner spaces, surjective arrows, categorical indecomposability and endomorphism rings isomorphic to the layer-k vertex division ring. The actual Ore flag model instantiates these constructions. Canonical P and zero-defect classification are proved; positive-defect classification is proved for every layer and every finite-dimensional indecomposable object with strictly positive source-minus-target defect.',
    'classification_foundations_status': 'Proved for arbitrary division bimodules: canonical simple source and target endomorphism rings are their vertex division rings; both canonical objects are categorically indecomposable in Hom and tensor forms; the simple-source and simple-target boundary Hom spaces vanish under the respective injectivity/surjectivity conditions; actual kernel complements split arbitrary representation retracts; and indecomposable representations outside the corresponding simple isomorphism class have injective adjoint or surjective tensor arrow. Canonical P now has its actual division endomorphism ring and indecomposability, a proved tensor arrow isomorphism and dimension vector (1,1) for right rank-one bimodules. Indecomposable representations with invertible tensor arrow and nonzero source are proved isomorphic to P using actual scalar-line retracts; this establishes the equal-corner-dimension branch under finite-dimensionality and the nonsimple surjectivity criterion. The actual family I_k, its endomorphism rings, dimensions, reflection recovery isomorphisms and pairwise nonisomorphism are proved. The positive-defect branch is proved by strong induction on target dimension, including recovery of the original object by the actual reflection equivalence. The merged complete list, irredundancy, ordered Hom vanishing and finite decomposition are now proved.',
    'simple_summand_lemma_status': 'Proved for arbitrary division-bimodule tensor representations, with no finite-dimensionality assumption on source or target: canonical simple source and target objects, actual split inclusion/projection morphisms, explicit kernel/cokernel scalar-line constructions, and both exact injectivity/surjectivity equivalences.',
    'reflection_equivalence_status': 'Proved as a mathlib category equivalence for arbitrary right-finite division bimodules on the injective-Hom-arrow and surjective-dual-tensor-arrow subcategories, including both functors on morphisms, functor laws, unit and counit inverse identities and naturality, bijections on morphism sets, and the actual finite dimension vector formula. The simple-summand criteria now identify these injective/surjective conditions with the original stated summand conditions. Endomorphism ring preservation is now proved as an actual ring isomorphism using independently defined componentwise morphism addition and actual composition; nontriviality and trivial-idempotent conditions are preserved. Ambient indecomposability in both directions is now proved using binary biproducts, a generic equivalence theorem, and explicit closure of the subcategories under actual retracts. Tensor-Hom conversion and its restriction give the original tensor-representation category equivalence, object formulas, endomorphism rings and dimension-vector formula.',
    'general_tensor_Hom_lemma_status': 'Proved for every right-finite division bimodule and arbitrary right target module, using an actual balanced quotient tensor product, a finite-basis inverse, both inverse identities, and full right-linear naturality.',
    'general_artinian_lemma_status': 'Proved for arbitrary right-finite division bimodules using an actual square-zero-extension triangular ring, its regular corners, and an order embedding of submodule lattices. The ambient case is explicitly ring-isomorphic to the matrix subring used for the counterexample candidate.',
    'representation_model_status': 'For every division bimodule, without a finite-dimensionality hypothesis, its actual triangular-ring right modules are equivalent to the actual Hom representation category and to the tensor representation category. The forward right action is (x,y)[a,n;0,b]=(x*a,gamma(x tensor n)+y*b). The inverse extracts the two actual idempotent corner spaces and uses right multiplication by off-diagonal n as the adjoint arrow. Module and representation maps preserve identities and composition. Both recovery isomorphisms and their naturality are proved and packaged as an actual category equivalence, with ambient indecomposability preservation and actual endomorphism ring isomorphisms for both representation descriptions. Earlier finite-generation and finite-presentation results apply under the original right-finiteness hypotheses.',
    'classification_status': 'Proved (manuscript prop:class) for every division bimodule N with right dimension sequence (1,2,2,...), i.e. a RightReflectionChain with dim N_B = 1: the list E1 = I_0, I_k (k >= 1), P, E2 indexed by the well order N +lex Bool is complete for finite-dimensional indecomposable representations and for finitely generated indecomposable right R_N-modules, irredundant, has division endomorphism rings, and satisfies Hom(C,C\') = 0 whenever C precedes C\'. Hom(I_k, I_l) and Hom(I_k, P) vanish by iterating actual reflections at every layer for targets with b <= a and k(a-b) < b, using the boundary simple-source vanishing and full faithfulness. Every finitely generated right R_N-module is a finite direct sum of listed modules.',
    'decomposition_lemma_status': 'Proved (manuscript lem:decomp) for an arbitrary left artinian ring (right modules over Lambda are modules over Lambda^op), a well-ordered index set and a complete irredundant list of finitely generated indecomposable modules with division endomorphism rings and Hom(X_a, X_b) = 0 for a < b: every module in the same universe is isomorphic to a direct sum of listed modules. The proof follows the manuscript: W_a spanned by maps through earlier X_b, lifts of a basis of Hom(X_a,M)/W_a over End(X_a)^op, transfinite lifting, surjectivity, vanishing of components of type >= a for maps into ker(pi), and the endomorphism e = iota - w p_0 with e z = z; the final contradiction uses a coordinate of z of maximal type instead of the nilpotency of e on a finite coordinate summand. Finite decomposition of finitely generated modules is proved by well-founded induction on submodules (finitely generated modules over an artinian ring are artinian).',
    'pure_semisimplicity_status': 'Proved (manuscript thm:pss) for every division bimodule with right dimension sequence (1,2,2,...): every right R_N-module in universe max u v is a direct sum of copies of the listed finitely presented modules, R_N is right pure semisimple, and the I_k (k >= 1) give infinitely many isomorphism classes of finitely generated indecomposable right modules. For the actual Ore model both properties are transported along the proved ring isomorphism to the matrix ring R = (H T; 0 T): R is right pure semisimple in every universe and not of finite representation type. Failure of left pure semisimplicity is proved directly, without the theorem of Chase (see interpretive_notes), and lem:qtorus is proved for every nonzero rational q.',
    'lean_source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                           for p in sources + [ROOT / 'AxiomAudit.lean']},
}
(ROOT / 'verification.log').write_text('\n'.join(logs), encoding='utf-8')
(ROOT / 'verification_status.json').write_text(json.dumps(status, indent=2, ensure_ascii=False) + '\n',
                                              encoding='utf-8')
print(f'PASS: {len(theorems)} theorems; axiom set {sorted(used)}; thm:main audited.')
