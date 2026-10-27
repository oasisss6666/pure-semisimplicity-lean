import QuantumFlags.SimpleEndomorphismRings
import QuantumFlags.EndRingIndecomposable
import QuantumFlags.TensorReflectionEquivalence
import QuantumFlags.TensorSimpleSummands

namespace QuantumFlags
noncomputable section
open CategoryTheory
universe u v
variable (N : DivisionBimodule.{u})

theorem simpleSource_indecomposable : Indecomposable (simpleSource.{u,v} N) :=
  indecomposable_of_endRingEquiv_division _ (simpleSourceEndRingEquiv N)

theorem simpleTarget_indecomposable : Indecomposable (simpleTarget.{u,v} N) :=
  indecomposable_of_endRingEquiv_division _ (simpleTargetEndRingEquiv N)

def tensorSimpleSourceEndRingEquiv : End (tensorSimpleSource.{u,v} N) ≃+* N.LeftRing :=
  (tensorHomEndRingEquiv N (tensorSimpleSource N)).trans (simpleSourceEndRingEquiv N)

def tensorSimpleTargetEndRingEquiv : End (tensorSimpleTarget.{u,v} N) ≃+* N.RightRing :=
  (tensorHomEndRingEquiv N (tensorSimpleTarget N)).trans (simpleTargetEndRingEquiv N)

theorem tensorSimpleSourceEndRingEquiv_exists :
    Nonempty (End (tensorSimpleSource.{u,v} N) ≃+* N.LeftRing) :=
  ⟨tensorSimpleSourceEndRingEquiv N⟩

theorem tensorSimpleTargetEndRingEquiv_exists :
    Nonempty (End (tensorSimpleTarget.{u,v} N) ≃+* N.RightRing) :=
  ⟨tensorSimpleTargetEndRingEquiv N⟩

theorem tensorSimpleSource_indecomposable : Indecomposable (tensorSimpleSource.{u,v} N) :=
  indecomposable_of_endRingEquiv_division _ (tensorSimpleSourceEndRingEquiv N)

theorem tensorSimpleTarget_indecomposable : Indecomposable (tensorSimpleTarget.{u,v} N) :=
  indecomposable_of_endRingEquiv_division _ (tensorSimpleTargetEndRingEquiv N)

end
end QuantumFlags
