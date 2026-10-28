import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalCone

/-! # Local Cone Reindex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalConeReindex.SemilatticeLocalConeReindex

noncomputable section

/-! The canonical local cone is compatible with reindexing whenever
the required intersection restrictions remain invertible. -/

open _root_.CategoryTheory Opposite

universe u v w z
variable (C : Type u) [SemilatticeInf C] (D : Type v) [SemilatticeInf D]
  {A : Type w} [Category.{z} A] (F : C ⥤ D) (I : C) (P : Dᵒᵖ ⥤ A)
  (hC : ∀ V : C, IsIso ((F.op ⋙ P).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))
  (hD : ∀ V : D, IsIso (P.map (homOfLE (inf_le_left : V ⊓ F.obj I ≤ V)).op))

theorem cone : LocalCone.SemilatticeLocalCone.cone C I (F.op ⋙ P) hC =
    Functor.whiskerLeft F.op (LocalCone.SemilatticeLocalCone.cone D (F.obj I) P hD) := by
  let η := Functor.whiskerLeft F.op (LocalCone.SemilatticeLocalCone.cone D (F.obj I) P hD)
  have hi : η.app (op I) = 𝟙 _ := LocalCone.SemilatticeLocalCone.self D (F.obj I) P hD
  have h := LocalCone.SemilatticeLocalCone.factorization C I (F.op ⋙ P) hC _ η
  apply NatTrans.ext
  funext V
  have hV := congrArg (fun a => a.app V) h
  change η.app V = η.app (op I) ≫ (LocalCone.SemilatticeLocalCone.cone C I (F.op ⋙ P) hC).app V at hV
  rw [hi, Category.id_comp] at hV
  exact hV.symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalConeReindex.SemilatticeLocalConeReindex
