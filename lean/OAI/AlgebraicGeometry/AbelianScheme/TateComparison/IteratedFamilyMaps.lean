import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConstantFamilyMaps
import OAI.ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison

/-! # Iterated Family Maps -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IteratedFamilyMaps

noncomputable section

/-! The constant-family descent theorem in the literal two-stage
pullback coordinates used by finite coefficient spreading. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian
variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  {S T : Scheme} (p : S ⟶ Spec (.of k)) (h : T ⟶ S)
  [LocallyOfFiniteType (h ≫ p)] [IsIntegral T]

theorem iteratedFamily_endomorphism_descends
    (y₀ : 𝟙_ (Over (Spec (.of k))) ⟶ Over.mk (h ≫ p))
    (a : ((A.pullback p).pullback h).scheme ⟶ ((A.pullback p).pullback h).scheme)
    [IsMonHom a] :
    ∃ f : A.scheme ⟶ A.scheme, IsMonHom f ∧
      ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism (A.pullback p) h
        (ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism A p f) = a := by
  have : LocallyOfFiniteType (Over.mk (h ≫ p)).hom :=
    inferInstanceAs (LocallyOfFiniteType (h ≫ p))
  have : IsIntegral (Over.mk (h ≫ p)).left := inferInstanceAs (IsIntegral T)
  let e := (A.pullbackCompIso p h).symm
  let b : (Over.pullback (h ≫ p)).obj A.scheme ⟶
      (Over.pullback (h ≫ p)).obj A.scheme := e.inv ≫ a ≫ e.hom
  have : IsMonHom b := inferInstanceAs (IsMonHom (e.inv ≫ a ≫ e.hom))
  obtain ⟨f, hf, hfb⟩ := ConstantFamilyMaps.constantFamily_endomorphism_descends A (Over.mk (h ≫ p)) y₀ b
  change (Over.pullback (h ≫ p)).map f = b at hfb
  refine ⟨f, hf, ?_⟩
  apply (cancel_mono e.hom).mp
  have hn : ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism (A.pullback p) h
      (ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism A p f) ≫ e.hom =
      e.hom ≫ (Over.pullback (h ≫ p)).map f := by
    change _ ≫ (A.pullbackCompIso p h).inv = (A.pullbackCompIso p h).inv ≫ _
    simp only [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv]
    exact (Over.pullbackComp h p).inv.naturality f
  exact hn.trans ((congrArg (fun z => e.hom ≫ z) hfb).trans
    (e.hom_inv_id_assoc (a ≫ e.hom)))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IteratedFamilyMaps
