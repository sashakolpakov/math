import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyLevelIsoSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.UniversalLevelRigidity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubsingletonSheafExistence

/-! # Modeled Target Iso Existence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ModeledTargetIsoExistence

noncomputable section

/-! At full level at least three, local existence of a complete
isomorphism to a modeled family implies global existence. The source
family and every test scheme remain arbitrary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S T : Scheme.{0}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (f : T ⟶ S)
    (B : PolarizationData.PolarizedAbelianWithFullLevel g δ N T) (hN : 3 ≤ N)

include hN

theorem modeledTargetPolarizedIsomorphisms_subsingleton :
    Subsingleton (Moduli.Isomorphisms.LevelPreservingIso B (A.pullback f)) := by
  let : Subsingleton (Moduli.Isomorphisms.LevelPreservingIso (A.pullback f) (A.pullback f)) :=
    LocallyNoetherian.UniversalLevelRigidity.polarizedPullbackIsomorphisms_subsingleton_of_locallyNoetherian A A hN (Over.mk f)
  refine ⟨fun e q => ?_⟩
  apply Moduli.Isomorphisms.LevelPreservingIso.ext_abelian
  apply (cancel_epi e.abelian.inv).mp
  exact congrArg (fun z : Moduli.Isomorphisms.LevelPreservingIso (A.pullback f) (A.pullback f) => z.abelian.hom)
    (Subsingleton.elim (e.symm.trans e) (e.symm.trans q))

theorem familyLevelIsoFunctor_obj_subsingleton_modeledTarget (V : Over T) :
    Subsingleton ((Family.LevelIsoFunctor.familyLevelIsoFunctor B (A.pullback f)).obj (.op V)) := by
  let : Subsingleton (Moduli.Isomorphisms.LevelPreservingIso (B.pullback V.hom) (A.pullback (V.hom ≫ f))) :=
    modeledTargetPolarizedIsomorphisms_subsingleton A (V.hom ≫ f) (B.pullback V.hom) hN
  exact (Moduli.Isomorphisms.LevelPreservingIso.transportEquiv
    (Moduli.Isomorphisms.LevelPreservingIso.refl (B.pullback V.hom))
    (Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A f V.hom)).injective.subsingleton

/-- Existence is local because both the isomorphism sheaf and its
full-level uniqueness have been proved for the modeled target. -/
theorem levelIso_nonempty_of_openCover_modeledTarget (C : T.OpenCover)
    (hlocal : ∀ i, Nonempty (Moduli.Isomorphisms.LevelPreservingIso (B.pullback (C.f i))
      ((A.pullback f).pullback (C.f i)))) :
    Nonempty (Moduli.Isomorphisms.LevelPreservingIso B (A.pullback f)) := by
  let P := Family.LevelIsoFunctor.familyLevelIsoFunctor B (A.pullback f)
  let V : C.I₀ → Over T := fun i => Over.mk (C.f i)
  let j : ∀ i, V i ⟶ Over.mk (𝟙 T) := fun i => Over.homMk (C.f i) (Category.comp_id _)
  let R := Sieve.ofArrows V j
  have hR : R ∈ (Scheme.zariskiTopology.over T) (Over.mk (𝟙 T)) := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact C.mem_grothendieckTopology
  have h : Nonempty (P.obj (.op (Over.mk (𝟙 T)))) := by
    apply SubsingletonSheafExistence.subsingletonSheaf_nonempty_of_cover (Scheme.zariskiTopology.over T) P
      (FamilyLevelIsoSheaf.familyLevelIsoFunctor_isSheaf_modeledTarget A f B)
      (fun V => familyLevelIsoFunctor_obj_subsingleton_modeledTarget A f B hN V.unop) R hR
    intro W c hc
    obtain ⟨i, a, _⟩ := (Sieve.mem_ofArrows_iff V j c).mp hc
    exact (hlocal i).map (P.map a.op)
  obtain ⟨q⟩ := h
  exact ⟨((Moduli.Isomorphisms.LevelPreservingIso.pullbackId B).symm.trans q).trans
    (Moduli.Isomorphisms.LevelPreservingIso.pullbackId (A.pullback f))⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ModeledTargetIsoExistence
