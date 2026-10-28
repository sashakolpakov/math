import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Objects

/-! # Lie Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The geometric Lie signature survives actual base change, using the
canonical comparison between iterated and composite pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {R : Type} [CommRing R] {g : ℕ} {S S' S'' : Scheme.{0}}
  (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (ρ : ActionData.IntegralAction R A)

theorem LieBaseChange.action_pullbackComp (f : S' ⟶ S) (h : S'' ⟶ S') (a : R) :
    (ρ.pullback (h ≫ f)).map a ≫ (A.pullbackCompIso f h).hom =
      (A.pullbackCompIso f h).hom ≫ ((ρ.pullback f).pullback h).map a := by
  let e := Functor.mapMonNatIso (Over.pullbackComp h f) ≪≫
    Functor.mapMonCompIso (F := Over.pullback f) (G := Over.pullback h)
  exact congrArg Mon.Hom.hom (e.hom.naturality (Mon.ofHom (ρ.map a)))

theorem LieBaseChange.hasLieRank_pullbackComp {k : Type} [Field k] (f : S' ⟶ S)
    (h : Spec (.of k) ⟶ S') (τ : R →+* k) (r : ℕ)
    (hr : LieRanks.HasLieRank (A.pullback (h ≫ f)) (ρ.pullback (h ≫ f)) τ r) :
    LieRanks.HasLieRank ((A.pullback f).pullback h) ((ρ.pullback f).pullback h) τ r :=
  LieTransport.hasLieRank_transport (ρ.pullback (h ≫ f)) ((ρ.pullback f).pullback h)
    (A.pullbackCompIso f h) (LieBaseChange.action_pullbackComp A ρ f h) τ r hr

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
  {T U : Over (Spec (.of K))}

omit [NumberField E] [NumberField.IsCMField E] [NumberField K] in
theorem PEL.Objects.HasPrescribedLieRanks.pullback
    (A : HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) U.left)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (hr : PEL.Objects.HasPrescribedLieRanks P iota U A ρ) (f : T ⟶ U) :
    PEL.Objects.HasPrescribedLieRanks P iota T (A.pullback f.left) (ρ.pullback f.left) := by
  intro F _ _ j q hq τ
  have hc : (q ≫ f.left) ≫ U.hom = Spec.map (CommRingCat.ofHom j) :=
    (Category.assoc _ _ _).trans ((congrArg (fun a => q ≫ a) f.w).trans hq)
  exact LieBaseChange.hasLieRank_pullbackComp A ρ f.left q _ _ (hr F j (q ≫ f.left) hc τ)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
