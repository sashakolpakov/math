import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.CohomologyEulerAdditivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.BinaryBiproduct

/-! # Coherent Euler Biprod -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.CoherentEulerBiprod

noncomputable section

/-! Binary Euler additivity from the actual split short exact sequence. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem proper_coherent_euler_biprod {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [M.IsFiniteType] [N.IsFiniteType] :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (M ⊞ N) =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p M + CohomologyEulerCharacteristic.coefficientEulerCharacteristic p N := by
  have := Coherent.BinaryBiproduct.module_biprod_quasicoherent M N
  have := Coherent.BinaryBiproduct.module_biprod_finiteType M N
  let S : ShortComplex X.Modules := ShortComplex.mk
    (biprod.inl : M ⟶ M ⊞ N) (biprod.snd : M ⊞ N ⟶ N) (by simp)
  let t : S.Splitting :=
    { r := biprod.fst
      s := biprod.inr
      f_r := by change biprod.inl ≫ biprod.fst = 𝟙 M; exact biprod.inl_fst
      s_g := by change biprod.inr ≫ biprod.snd = 𝟙 N; exact biprod.inr_snd
      id := by
        change (biprod.fst : M ⊞ N ⟶ M) ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (M ⊞ N)
        exact biprod.total }
  exact @CohomologyEulerAdditivity.proper_coherent_euler_additive k _ X p _ S t.shortExact
    (inferInstance : M.IsQuasicoherent) (inferInstance : M.IsFiniteType)
    (Coherent.BinaryBiproduct.module_biprod_quasicoherent M N) (Coherent.BinaryBiproduct.module_biprod_finiteType M N)
    (inferInstance : N.IsQuasicoherent) (inferInstance : N.IsFiniteType)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.CoherentEulerBiprod
