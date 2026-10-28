import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
import OAI.AlgebraicGeometry.AbelianScheme.HomExtension

/-! # Extending Endomorphisms -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExtendingEndomorphisms.CM

noncomputable section

/-! Every actual endomorphism of the number-field abelian variety extends
over its good-reduction model. The extension is derived from proved HomExtension,
with the exact generic-fiber compatibility required by GeometricComparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {R L K : Type}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L] [Field K]
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K)))
  (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of R))) (j : K →+* L)
  (e : (B.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).scheme ≅
    (A.pullback (Spec.map (CommRingCat.ofHom j))).scheme) [IsMonHom e.hom]

/-- The generic-fiber isomorphism is part of the actual model; extension
and its compatibility with that isomorphism are proved here. -/
theorem exists_compatible_integral_endomorphism (f : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.scheme) :
    ∃ h : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd B.scheme,
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).map h.toMul.hom.hom ≫
        e.hom = e.hom ≫ (Over.pullback (Spec.map (CommRingCat.ofHom j))).map f.toMul.hom.hom := by
  let f₀ : A.scheme ⟶ A.scheme := f.toMul.hom.hom
  let : IsMonHom f₀ := f.toMul.hom.isMonHom_hom
  let : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom j))).obj A.scheme) :=
    Functor.grpObjObj (F := Over.pullback (Spec.map (CommRingCat.ofHom j)))
  let fA : (A.pullback (Spec.map (CommRingCat.ofHom j))).scheme ⟶
      (A.pullback (Spec.map (CommRingCat.ofHom j))).scheme :=
    (Over.pullback (Spec.map (CommRingCat.ofHom j))).map f₀
  let : IsMonHom fA := inferInstanceAs
    (IsMonHom ((Over.pullback (Spec.map (CommRingCat.ofHom j))).map f₀))
  let fL := e.hom ≫ fA ≫ e.inv
  have hfL : IsMonHom fL := inferInstanceAs (IsMonHom (e.hom ≫ fA ≫ e.inv))
  obtain ⟨h, hh, _hunique⟩ := AbelianScheme.HomExtension.neron_extension_of_abelian_hom
    (K := L) B.scheme B.scheme fL hfL
  let : IsMonHom h := hh.1
  refine ⟨Additive.ofMul (Grp.ofHom h), ?_⟩
  change (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).map h ≫
    e.hom = _
  rw [hh.2]
  exact (Category.assoc e.hom (fA ≫ e.inv) e.hom).trans
    (congrArg (fun k => e.hom ≫ k)
      ((Category.assoc fA e.inv e.hom).trans
        ((congrArg (fun k => fA ≫ k) e.inv_hom_id).trans (Category.comp_id fA))))

def integralExtension (f : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.scheme) : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd B.scheme :=
  (exists_compatible_integral_endomorphism A B j e f).choose

theorem integralExtension_compatible (f : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.scheme) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).map
        (integralExtension A B j e f).toMul.hom.hom ≫ e.hom =
      e.hom ≫ (Over.pullback (Spec.map (CommRingCat.ofHom j))).map f.toMul.hom.hom :=
  (exists_compatible_integral_endomorphism A B j e f).choose_spec

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExtendingEndomorphisms.CM
