import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FlagComposites
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Lattices

/-! # Initial Flag Lattice -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The initial actual composite has exactly the source integral Tate
lattice, including the equality transport at the flag's initial point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem PELModuli.PELFamilyIso.ofEq_tatePreimage {R : Type} [CommRing R] {g N : ℕ} {S : Scheme}
    {P Q : PEL.PELFamilyData R g N S} (h : P = Q) (T : Over S) (q : ℕ) [Fact q.Prime] :
    Rational.isogenyTatePreimage (T := T) (q := q) (PELModuli.PELFamilyIso.ofEq h).abelian.hom =
      Rational.integralTateImage P.abelian.scheme T q := by
  subst Q
  exact Lattices.isogenyTatePreimage_id T q

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)
  {k : Type} [Field k] {b : Spec (.of k) ⟶ Spec (.of K)}
  {x : D.GeometricPoint b} {ts : List (Local.IntegralType s)}

theorem Data.SphericalPELAlbaneseData.initialFlagIsogeny_tatePreimage (F : D.PELFlag b x ts) :
    Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
      (D.initialFlagIsogeny F).isogeny.hom =
      Rational.integralTateImage (D.fiberFamily b x).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q :=
  PELModuli.PELFamilyIso.ofEq_tatePreimage (congrArg (D.fiberFamily b) F.start.symm) _ q

theorem Data.SphericalPELAlbaneseData.c46FlagComposites_zero_tatePreimage (h : D.RealizesIsogenyQuotient) (F : D.PELFlag b x ts) :
    Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
      (D.c46FlagComposites h F 0).isogeny.hom =
      Rational.integralTateImage (D.fiberFamily b x).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q :=
  D.initialFlagIsogeny_tatePreimage F

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
