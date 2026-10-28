import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELAutomorphismDescent
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexFiberRigidity
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricFieldModel
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELCoherence

/-! # Geometric PEL Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricPELRigidity

noncomputable section

/-! Full marked polarized PEL automorphisms of every geometric moduli
fiber are trivial. A countable field of definition connects the actual
fiber to a complex fiber; endomorphism descent handles arbitrary cardinality. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

namespace PELFamilyIso

variable {R L k C : Type} [CommRing R] [Field L] [IsAlgClosed L] [Field k] [Field C]
  {g N : ℕ}

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso.abelian_eq_id_of_common_model
    (bk : Spec (.of k) ⟶ Spec (.of L)) (bc : Spec (.of C) ⟶ Spec (.of L))
    (P : PEL.PELFamilyData R g N (Spec (.of L)))
    (Pk : PEL.PELFamilyData R g N (Spec (.of k)))
    (Pc : PEL.PELFamilyData R g N (Spec (.of C)))
    (ak : PELModuli.PELFamilyIso Pk (P.pullback bk)) (ac : PELModuli.PELFamilyIso Pc (P.pullback bc))
    (hr : ∀ j : PELModuli.PELFamilyIso Pc Pc, j.abelian.hom = 𝟙 Pc.abelian.scheme)
    (e : PELModuli.PELFamilyIso Pk Pk) : e.abelian.hom = 𝟙 Pk.abelian.scheme := by
  apply PELModuli.PELFamilyIso.abelian_eq_id_via e ak
  intro j
  apply PELModuli.PELFamilyIso.abelian_eq_id_of_rigid_extension P bk bc _ j
  intro l
  exact PELModuli.PELFamilyIso.abelian_eq_id_via l ac.symm hr

end PELFamilyIso

namespace SphericalPELAlbaneseData

local notation "fiberBase" => Spec (@CommRingCat.of ℂ (@Field.toCommRing ℂ Complex.instField))

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (h : D.HasIntegralModelGeometry)
  {k : Type} [Field k] [IsAlgClosed k]

include h in
theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.geometricFiber_abelian_eq_id
    (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b)
    (e : PELModuli.PELFamilyIso (D.fiberFamily b x) (D.fiberFamily b x)) :
    e.abelian.hom = 𝟙 (D.fiberFamily b x).abelian.scheme := by
  have : Countable K := Cardinal.mk_le_aleph0_iff.mp
    ((Algebra.IsAlgebraic.cardinalMk_le_max ℚ K).trans
      (max_le Cardinal.mk_le_aleph0 le_rfl))
  have : Smooth D.model.space.hom := h.smooth
  have : LocallyOfFiniteType D.space.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd D.model.space.hom D.generic))
  obtain ⟨M⟩ := GeometricFieldModel.geometricPoint_has_countable_model K D.space.hom x.left
  let bk := Spec.map (CommRingCat.ofHom M.toOriginal)
  let bc : fiberBase ⟶ Spec (.of M.field) := Spec.map (CommRingCat.ofHom M.toComplex)
  let bL := M.point ≫ D.space.hom
  let xc : D.GeometricPoint (bc ≫ bL) := Over.homMk (bc ≫ M.point) (Category.assoc _ _ _)
  exact PELModuli.PELFamilyIso.abelian_eq_id_of_common_model bk bc
    (D.family.pullback M.point) (D.fiberFamily b x) (D.fiberFamily (bc ≫ bL) xc)
    (D.family.pullbackFactor bk M.point x.left M.factor)
    (D.family.pullbackFactor bc M.point (bc ≫ M.point) rfl)
    (fun j => D.complexFiber_abelian_eq_id h (bc ≫ bL) xc j) e

end SphericalPELAlbaneseData

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricPELRigidity
