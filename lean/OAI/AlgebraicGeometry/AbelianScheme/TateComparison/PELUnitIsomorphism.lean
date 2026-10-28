import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.KernelDetermination
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELTransport
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.DualFactorization

/-! # PEL Unit Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! A multiplier-one PEL isogeny is an actual isomorphism of the complete
marked polarized family. The dual isomorphism follows from the Poincare
universal property and the raw bundle equation is preserved. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj BigOperators

open OAI.AlgebraicGeometry.AbelianScheme.CentralAction.DualFactorization.Construction

universe u
variable {R : Type u} [CommRing R] {g N n : ℕ} {S : Scheme.{u}}
  {P Q : PEL.PELFamilyData R g N S}

theorem PELIsogenies.PELIsogeny.dualHom_isIso_of_isogeny_isIso (e : PELIsogenies.PELIsogeny P Q n) [IsIso e.isogeny.hom] :
    IsIso e.dualHom := by
  let j := (asIso e.isogeny.hom).symm
  have : IsMonHom (asIso e.isogeny.hom).hom := e.isogeny.preservesGroup
  have : IsMonHom j.hom := inferInstanceAs (IsMonHom (asIso e.isogeny.hom).inv)
  have hd : (CentralAction.DualPicard.Construction.dualUnderlyingIso Q.dual P.dual j).hom ≫ e.dualHom = 𝟙 P.dual.abelian.scheme :=
    CentralAction.DualFactorization.Construction.dual_quotient_factorization e (PELIsogenies.PELIsogeny.identity P) j (IsIso.hom_inv_id e.isogeny.hom)
  have he : e.dualHom = (CentralAction.DualPicard.Construction.dualUnderlyingIso Q.dual P.dual j).inv := by
    apply (cancel_epi (CentralAction.DualPicard.Construction.dualUnderlyingIso Q.dual P.dual j).hom).mp
    rw [hd, Iso.hom_inv_id]
  rw [he]
  infer_instance

def PELIsogenies.PELIsogeny.toFamilyIsoOfIsIso (e : PELIsogenies.PELIsogeny P Q 1) [IsIso e.isogeny.hom] : PELModuli.PELFamilyIso P Q := by
  have := e.dualHom_isIso_of_isogeny_isIso
  have : IsMonHom (asIso e.dualHom).hom := e.dualGroup
  refine {
    abelian := asIso e.isogeny.hom
    dual := (asIso e.dualHom).symm
    abelianGroup := inferInstance
    dualGroup := inferInstanceAs (IsMonHom (asIso e.dualHom).inv)
    polarization := ?_
    poincare := ?_
    equivariant := e.equivariant
    marking := e.marking }
  · change P.polarizationMap.hom ≫ inv e.dualHom = e.isogeny.hom ≫ Q.polarizationMap.hom
    have hp : e.isogeny.hom ≫ Q.polarizationMap.hom ≫ e.dualHom = P.polarizationMap.hom := by
      simpa only [pow_one] using e.polarization
    rw [← hp]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · have hp := congrArg
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (inv e.dualHom ⊗ₘ 𝟙 P.abelian.scheme).left) e.poincare
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← Over.comp_left, tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp] at hp
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← Over.comp_left, tensorHom_comp_tensorHom,
      IsIso.inv_hom_id, Category.id_comp, tensorHom_id, id_whiskerRight, Over.id_left,
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id] at hp
    exact hp

variable {k R₀ : Type} [Field k] [CharZero k] [IsAlgClosed k] [CommRing R₀]
  {P₀ Q₀ : PEL.PELFamilyData R₀ g N (Spec (.of k))}
  (e : PELIsogenies.PELIsogeny P₀ Q₀ 1) (q : ℕ) [Fact q.Prime]
  (δ : Fin g → ℕ) (hP : P₀.polarizationMap.HasPolarizationType δ)
  (hQ : Q₀.polarizationMap.HasPolarizationType δ) (hq : Nat.Coprime q (∏ i, δ i))

include q δ hP hQ hq in
theorem PELIsogenies.PELIsogeny.multiplier_one_isIso : IsIso e.isogeny.hom := by
  let f : PELIsogenies.PELIsogeny P₀ Q₀ (q ^ 0) := e.castMultiplier (pow_zero q).symm
  have hmono : Mono e.isogeny.hom := by
    constructor
    intro T a b hab
    have hh : (a / b) ≫ f.isogeny.hom = 1 := by
      rw [PELIsogenies.PELIsogeny.castMultiplier_hom, GrpObj.div_comp, hab, div_self']
    have hk := f.kernel_killed_all_tests δ hP hQ hq T (a / b) hh
    simpa only [pow_zero, pow_one, div_eq_one] using hk
  have := CentralAction.Quotient.Construction.isogeny_effectiveEpi e.isogeny
  let j := EffectiveEpi.desc e.isogeny.hom (𝟙 P₀.abelian.scheme)
    (fun _ _ h => by simpa only [Category.comp_id] using (cancel_mono e.isogeny.hom).mp h)
  have hj : e.isogeny.hom ≫ j = 𝟙 P₀.abelian.scheme := EffectiveEpi.fac _ _ _
  refine ⟨⟨j, hj, ?_⟩⟩
  apply (cancel_epi e.isogeny.hom).mp
  rw [← Category.assoc, hj, Category.id_comp, Category.comp_id]

def PELIsogenies.PELIsogeny.multiplierOneFamilyIso : PELModuli.PELFamilyIso P₀ Q₀ := by
  have := e.multiplier_one_isIso q δ hP hQ hq
  exact e.toFamilyIsoOfIsIso

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
