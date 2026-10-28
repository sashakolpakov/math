import OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary
import OAI.RepresentationTheory.Weil.AdelicSplitting.Integral

/-! # Integral Topology -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntegralTopology

noncomputable section

/-! Openness of the integral subgroups used in the actual restricted
unitary product. This uses the order O_v[δ] from AdelicSplitting, including split places. -/

open scoped _root_.NumberField _root_.Topology

open OAI.RepresentationTheory.Weil.AdelicSplitting.Integral.Construction OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

theorem localIntegerRing_open (F : Type*) [Field F] [NumberField F] (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    IsOpen (Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v : Set (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)) := by
  cases v with
  | inl v => exact isOpen_univ
  | inr v => exact Valued.isOpen_integer (v.adicCompletion F)

theorem quadraticOrder_open (F : Type*) [Field F] [NumberField F] (d : F) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    IsOpen (Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v : Set (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v)) := by
  have ho : IsOpen {z : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v |
      z.re ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v ∧ z.im ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v} :=
    ((localIntegerRing_open F v).preimage (Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_re _)).inter
      ((localIntegerRing_open F v).preimage (Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_im _))
  apply (Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v).toAddSubgroup.isOpen_of_mem_nhds
  apply Filter.mem_of_superset (ho.mem_nhds (x := 0) ?_)
  · intro z hz
    exact Weil.AdelicSplitting.Integral.Construction.quadraticOrder_of_coeff F d v z hz.1 hz.2
  · exact ⟨(Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v).zero_mem, (Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v).zero_mem⟩

theorem integralMatrixGroup_open
    {R G I : Type*} [CommRing R] [Group G] [Fintype I] [DecidableEq I]
    [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : G →* Matrix I I R) (hρ : Continuous ρ)
    (S : Subring R) (hS : IsOpen (S : Set R)) :
    IsOpen (Weil.AdelicSplitting.Integral.Construction.integralMatrixGroup ρ S : Set G) := by
  have hm : IsOpen {g : G | ∀ i j, ρ g i j ∈ S} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hS.preimage ((continuous_apply j).comp ((continuous_apply i).comp hρ))
  exact hm.inter (hm.preimage continuous_inv)

theorem localUnitaryIntegral_open
    (F : Type*) [Field F] [NumberField F] {n : ℕ} {d : F}
    (H : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    IsOpen (Weil.AdelicSplitting.Integral.Construction.localUnitaryIntegral F H v : Set (Weil.AdelicSplitting.Integral.Construction.LocalUnitary F H v)) := by
  apply integralMatrixGroup_open
  · exact Units.continuous_val.comp continuous_subtype_val
  · exact quadraticOrder_open F d v

def localSUIntegral
    (F : Type*) [Field F] [NumberField F] {n : ℕ} {d : F}
    (H : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    Subgroup (SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H v)) :=
  (Weil.AdelicSplitting.Integral.Construction.localUnitaryIntegral F H v).comap (SpecialUnitary.includeUnitary (Weil.AdelicSplitting.Integral.Construction.localizedForm F H v))

theorem localSUIntegral_open
    (F : Type*) [Field F] [NumberField F] {n : ℕ} {d : F}
    (H : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    IsOpen (localSUIntegral F H v : Set (SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H v))) :=
  (localUnitaryIntegral_open F H v).preimage (SpecialUnitary.includeUnitaryContinuous _).continuous

end

end OAI.RepresentationTheory.Theta.Adelic.IntegralTopology
