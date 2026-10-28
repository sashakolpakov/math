import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Etale
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.PointedLifts

/-! # Unit Multiplication -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.UnitMultiplication

noncomputable section

/-! Unit multiplication and its two-sided factors are finite étale and
surjective over an arbitrary arithmetic base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]

theorem unit_multiplication_finite_etale_surjective
    (n : ℕ) (hn : ∀ s : S, IsUnit (n : S.presheaf.stalk s)) :
    IsFinite (((𝟙 A : A ⟶ A) ^ n).left) ∧
      Etale (((𝟙 A : A ⟶ A) ^ n).left) ∧ Surjective (((𝟙 A : A ⟶ A) ^ n).left) := by
  let p : A ⟶ A := (𝟙 A : A ⟶ A) ^ n
  have he : Etale p.left := AbelianScheme.TorsionQuotient.Etale.TorsionEtale.power_etale A n hn
  have hp : IsProper p.left := AbelianScheme.TorsionQuotient.Quasi.TorsionGeometry.power_isProper A n
  have hf : IsFinite p.left := AbelianScheme.TorsionQuotient.Quasi.TorsionGeometry.finite_of_proper_formallyUnramified p.left
  let z : S ⟶ A.left := η[A].left
  have hz : z ≫ A.hom = 𝟙 S := η[A].w
  have hpoint : (1 : 𝟙_ (Over S) ⟶ A) ≫ p = 1 := by
    simp only [p, MonObj.comp_pow, Category.comp_id, one_pow]
  have hpoint' : z ≫ p.left = z := congrArg Over.Hom.left hpoint
  have hcl : IsClopen (Set.range p.left) := ⟨by
    simpa only [Set.image_univ] using p.left.isClosedMap Set.univ isClosed_univ,
    p.left.isOpenMap.isOpen_range⟩
  have hsec : Set.range z ⊆ Set.range p.left := by
    rintro _ ⟨s, rfl⟩
    exact ⟨z s, congrArg (fun f : S ⟶ A.left => f s) hpoint'⟩
  have hr := Relative.PointedLifts.clopen_eq_univ_of_connected_fibers_and_section A.hom z
    (fun s => congrArg (fun f : S ⟶ S => f s) hz)
    A.hom.isConnected_preimage_singleton hcl hsec
  exact ⟨hf, he, ⟨Set.range_eq_univ.mp hr⟩⟩

theorem unit_multiplication_factor_finite_etale_surjective
    (f g : A ⟶ A) (n : ℕ) (hn : ∀ s : S, IsUnit (n : S.presheaf.stalk s))
    (hfg : f ≫ g = (𝟙 A : A ⟶ A) ^ n)
    (hgf : g ≫ f = (𝟙 A : A ⟶ A) ^ n) :
    IsFinite f.left ∧ Etale f.left ∧ Surjective f.left := by
  obtain ⟨hpFinite, hpEtale, hpSurj⟩ := unit_multiplication_finite_etale_surjective A n hn
  have hfg' : f.left ≫ g.left = ((𝟙 A : A ⟶ A) ^ n).left := congrArg Over.Hom.left hfg
  have hgf' : g.left ≫ f.left = ((𝟙 A : A ⟶ A) ^ n).left := congrArg Over.Hom.left hgf
  have : IsProper (g.left ≫ A.hom) := g.w.symm ▸ inferInstanceAs (IsProper A.hom)
  have : IsProper g.left := IsProper.of_comp g.left A.hom
  have : IsFinite (f.left ≫ g.left) := hfg' ▸ hpFinite
  have : Etale (f.left ≫ g.left) := hfg' ▸ hpEtale
  have : Etale (g.left ≫ f.left) := hgf' ▸ hpEtale
  have : FormallyUnramified g.left := FormallyUnramified.of_comp g.left f.left
  have hf : IsFinite f.left := IsFinite.of_comp f.left g.left
  have he : Etale f.left := Etale.of_comp f.left g.left
  have hs : Surjective (g.left ≫ f.left) := hgf' ▸ hpSurj
  exact ⟨hf, he, ⟨fun x => by
    obtain ⟨y, hy⟩ := hs.surj x
    exact ⟨g.left y, hy⟩⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.UnitMultiplication
