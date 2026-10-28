import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.PullbackInjection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.IsoCalculus
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseChange

/-! # Preservation Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.PreservationDescent

noncomputable section

/-! Preservation of the original ordered level descends from a
surjective base change. In particular an inverse polarized comparison
on that base change determines the level on the original family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseChange

variable {S T : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}

theorem fullLevel_transport_congr {A B : HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (α : A.FullLevel N)
    (e d : A.scheme ≅ B.scheme) [IsMonHom e.hom] [IsMonHom d.hom] (h : e = d) :
    α.transport (B := B) e = α.transport (B := B) d := by
  subst d
  rfl

theorem levelIso_transport_level {A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S} (j : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B) :
    A.level.transport (A := A.abelian) (B := B.abelian) j.abelian = B.level := by
  apply HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  exact j.level

theorem fullLevel_preservation_of_pullback [NeZero N] {A B : HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (α : A.FullLevel N) (β : B.FullLevel N) (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (b : T ⟶ S) [Surjective b]
    (h : (α.pullback b).transport (B := B.pullback b) (IsoCalculus.abelianPullbackIso e b) = β.pullback b) :
    α.transport (B := B) e = β := by
  apply PullbackInjection.fullLevel_pullback_injective B b
  exact (IsoCalculus.fullLevel_transport_pullback α e b).trans h

theorem fullLevel_preservation_of_inverse_reduction [NeZero N]
    (A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (e : A.abelian.scheme ≅ B.abelian.scheme) [IsMonHom e.hom]
    (b : T ⟶ S) [Surjective b] (j : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (B.pullback b) (A.pullback b))
    (h : IsoCalculus.abelianPullbackIso e b = j.abelian.symm) :
    A.level.transport (A := A.abelian) (B := B.abelian) e = B.level := by
  let er : (A.pullback b).abelian.scheme ≅ (B.pullback b).abelian.scheme := IsoCalculus.abelianPullbackIso e b
  have : IsMonHom er.hom := by
    dsimp only [er, HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.pullback]
    exact IsoCalculus.abelianPullbackIso_isMonHom e b
  have : IsMonHom j.abelian.symm.hom := j.symm.abelianGroup
  apply fullLevel_preservation_of_pullback (A := A.abelian) (B := B.abelian) A.level B.level e b
  exact (fullLevel_transport_congr (A := (A.pullback b).abelian) (B := (B.pullback b).abelian)
    (A.level.pullback b) er j.abelian.symm h).trans
    (levelIso_transport_level j.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.PreservationDescent
