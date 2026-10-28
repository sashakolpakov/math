import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.GroupObjects

/-! # Isogeny Polarization Symmetry -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.IsogenyPolarizationSymmetry

noncomputable section

/-! The reverse polarization relation follows from the actual paired
quotient identities and epimorphism cancellation. This is the algebraic
symmetry needed to swap the two projections of a Hecke correspondence.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

theorem paired_quotient_polarization_adjoint
    {S : Scheme.{u}} {A B DA DB : Over S} [GrpObj A] [GrpObj DA]
    (q : A ⟶ B) (v : B ⟶ A) [Epi q] (qd : DB ⟶ DA)
    («λA» : A ⟶ DA) [IsMonHom «λA»] («λB» : B ⟶ DB) (n : ℕ)
    (hqv : q ≫ v = (𝟙 A) ^ n)
    (hpol : q ≫ «λB» ≫ qd = «λA» ^ n) :
    «λB» ≫ qd = v ≫ «λA» := by
  apply (cancel_epi q).mp
  rw [hpol, ← Category.assoc, hqv, MonObj.pow_comp, Category.id_comp]

theorem paired_quotient_polarization_relation_symmetric
    {S : Scheme.{u}} {A B DA DB : Over S}
    [GrpObj A] [GrpObj DA] [GrpObj DB]
    (q : A ⟶ B) (v : B ⟶ A) [Epi q] [Epi v]
    (qd : DB ⟶ DA) (vd : DA ⟶ DB)
    («λA» : A ⟶ DA) [IsMonHom «λA»] («λB» : B ⟶ DB) (n : ℕ)
    (hqv : q ≫ v = (𝟙 A) ^ n)
    (hdual : qd ≫ vd = (𝟙 DB) ^ n)
    (hpol : q ≫ «λB» ≫ qd = «λA» ^ n) :
    v ≫ «λA» ≫ vd = «λB» ^ n := by
  have hp : ((𝟙 A) ^ n) ≫ «λA» = «λA» ^ n := by
    rw [MonObj.pow_comp, Category.id_comp]
  apply (cancel_epi (v ≫ q)).mp
  calc
    (v ≫ q) ≫ (v ≫ «λA» ≫ vd) = v ≫ (((q ≫ v) ≫ «λA») ≫ vd) := by
      simp only [Category.assoc]
    _ = v ≫ ((((𝟙 A) ^ n) ≫ «λA») ≫ vd) := by rw [hqv]
    _ = v ≫ ((«λA» ^ n) ≫ vd) := congrArg (fun k => v ≫ (k ≫ vd)) hp
    _ = v ≫ ((q ≫ «λB» ≫ qd) ≫ vd) := by rw [← hpol]
    _ = (v ≫ q) ≫ («λB» ≫ (qd ≫ vd)) := by simp only [Category.assoc]
    _ = (v ≫ q) ≫ («λB» ≫ (𝟙 DB) ^ n) := by rw [hdual]
    _ = (v ≫ q) ≫ «λB» ^ n := by rw [MonObj.comp_pow, Category.comp_id]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.IsogenyPolarizationSymmetry
