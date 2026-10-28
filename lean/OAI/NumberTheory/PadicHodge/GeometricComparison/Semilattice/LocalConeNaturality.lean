import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalCone

/-! # Local Cone Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalConeNaturality.SemilatticeLocalConeNaturality

noncomputable section

/-! Canonical chart cones commute with restriction to subcharts,
natural coefficient maps and additive-free changes of coefficient category. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w z t
variable (C : Type u) [SemilatticeInf C] {A : Type v} [Category.{w} A]
  (I : C) (P : Cᵒᵖ ⥤ A)
  (hP : ∀ V : C, IsIso (P.map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))

theorem app_of_le (J : C) (hJI : J ≤ I) :
    (LocalCone.SemilatticeLocalCone.cone C I P hP).app (op J) = P.map (homOfLE hJI).op := by
  let := hP J
  apply (cancel_mono (P.map (homOfLE (inf_le_left : J ⊓ I ≤ J)).op)).mp
  exact (LocalCone.SemilatticeLocalCone.app_comp C I P hP J).trans
    ((congrArg P.map (Subsingleton.elim _ _)).trans (P.map_comp _ _))

theorem transition (J : C) (hJI : J ≤ I) (Q : Cᵒᵖ ⥤ A)
    (hQ : ∀ V : C, IsIso (Q.map (homOfLE (inf_le_left : V ⊓ J ≤ V)).op))
    (α : P ⟶ Q) :
    LocalCone.SemilatticeLocalCone.cone C I P hP ≫ α =
      (Functor.const Cᵒᵖ).map (P.map (homOfLE hJI).op ≫ α.app (op J)) ≫ LocalCone.SemilatticeLocalCone.cone C J Q hQ := by
  have h := LocalCone.SemilatticeLocalCone.factorization C J Q hQ (P.obj (op I))
    (LocalCone.SemilatticeLocalCone.cone C I P hP ≫ α)
  rw [NatTrans.comp_app, app_of_le C I P hP J hJI] at h
  exact h

variable {B : Type z} [Category.{t} B] (F : A ⥤ B)

def mappedCone : (Functor.const Cᵒᵖ).obj (F.obj (P.obj (op I))) ⟶ P ⋙ F :=
  (Functor.constComp Cᵒᵖ (P.obj (op I)) F).inv ≫
    Functor.whiskerRight (LocalCone.SemilatticeLocalCone.cone C I P hP) F

theorem mappedCone_app (V : Cᵒᵖ) : (mappedCone C I P hP F).app V =
    F.map ((LocalCone.SemilatticeLocalCone.cone C I P hP).app V) := Category.id_comp _

theorem functor_naturality
    (hQ : ∀ V : C, IsIso ((P ⋙ F).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op)) :
    mappedCone C I P hP F = LocalCone.SemilatticeLocalCone.cone C I (P ⋙ F) hQ := by
  have h := LocalCone.SemilatticeLocalCone.factorization C I (P ⋙ F) hQ (F.obj (P.obj (op I))) (mappedCone C I P hP F)
  rw [mappedCone_app, LocalCone.SemilatticeLocalCone.self] at h
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalConeNaturality.SemilatticeLocalConeNaturality
