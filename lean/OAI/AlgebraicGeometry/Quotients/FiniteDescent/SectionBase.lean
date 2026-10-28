import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackScalarsValue

/-! # Section Base -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionBase.Construction.SectionBaseChange

/-! The nonvanishing locus of a line-bundle section commutes with arbitrary base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

theorem nonvanishing_pullback_comp (f : Y ⟶ Z) (g : X ⟶ Y)
    {M : Z.Modules} (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z ⟶ M) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection g (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s)) =
      AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (g ≫ f) s) := by
  apply congrArg sSup
  ext U
  change IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection g (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s))) ↔
    IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (g ≫ f) s))
  rw [AbelianModuli.HilbertConstruction.Section.Nonvanishing.isIso_pullbackSection_comp_iff g U.ι (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s),
    AbelianModuli.HilbertConstruction.Section.Nonvanishing.isIso_pullbackSection_comp_iff f (U.ι ≫ g) s,
    AbelianModuli.HilbertConstruction.Section.Nonvanishing.isIso_pullbackSection_comp_iff (g ≫ f) U.ι s, Category.assoc]

theorem nonvanishing_pullback_targetIso (f : X ⟶ Y) {M N : Y.Modules}
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ M) (e : M ≅ N) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f (s ≫ e.hom)) =
      AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) := by
  have he : AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f (s ≫ e.hom) =
      AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s ≫ ((Scheme.Modules.pullback f).mapIso e).hom := by
    simp only [AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection, Functor.map_comp, Category.assoc, Functor.mapIso_hom]
  rw [he, AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso]

/-- This equality holds for all scheme morphisms, including closed fibers
and nonreduced base changes. -/
theorem nonvanishing_pullback (f : X ⟶ Y) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L.sheaf) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) = f ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s := by
  ext x
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyTrivial (f x)
  let V : X.Opens := f ⁻¹ᵁ U
  let y : V.toScheme := ⟨x, hxU⟩
  have hcomp : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection V.ι (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s)) =
      AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (f ∣_ U) (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s)) :=
    (nonvanishing_pullback_comp f V.ι s).trans
      ((congrArg (fun k : V.toScheme ⟶ Y => AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection k s))
        (morphismRestrict_ι f U).symm).trans
          (nonvanishing_pullback_comp U.ι (f ∣_ U) s).symm)
  have hlocal : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection V.ι (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s)) =
      (f ∣_ U) ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s) := by
    rw [hcomp, ← nonvanishing_pullback_targetIso (f ∣_ U) (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s) e]
    rw [PullbackScalarsValue.Construction.PullbackScalars.nonvanishing_pullback_scalar, AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso]
  rw [AbelianModuli.HilbertConstruction.Section.Nonvanishing.sectionNonvanishing_pullback V.ι, AbelianModuli.HilbertConstruction.Section.Nonvanishing.sectionNonvanishing_pullback U.ι] at hlocal
  have hy : U.ι ((f ∣_ U) y) = f x :=
    congrArg (fun k : V.toScheme ⟶ Y => k y) (morphismRestrict_ι f U)
  have hm := congrArg (fun W : V.toScheme.Opens => y ∈ W) hlocal |>.to_iff
  change x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) ↔
    U.ι ((f ∣_ U) y) ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s at hm
  rw [hy] at hm
  exact hm

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionBase.Construction.SectionBaseChange
