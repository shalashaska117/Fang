# Checkpoint V4, 15 novembre 2026

Lavoro sospeso su richiesta di Pietro. Non riprendere test o implementazione senza una sua richiesta. La V4 e tutti i suoi 26 punti originali restano incompleti: questo checkpoint non cambia l'obiettivo.

## Directory e stato pubblicato

- Worktree: `C:/Users/ppell/Desktop/Github/_scratch/fang-v4-start-20261114`.
- Branch: `work/v4-start`.
- Ultimo aggiornamento verificato su GitHub prima di questo checkpoint: `f4235b871aa2acc8ff608163c90b73328ae285fc`, con i risultati della composizione EPR e dell'assemblaggio.
- Installazione qualificata ancora basata su `a3cdb5f5763d79380d789425ab4276748c977510`: `/var/tmp/fang-v4-goal-resolve-installation-v1-20261115/install/bin/fang`.
- Stato locale dettagliato: `experiments/V4-STATE.json`.
- Checklist: [docs/V4-CHECKLIST.md](docs/V4-CHECKLIST.md), 145 voci verificate e 92 aperte. Il conteggio non misura la percentuale di tempo restante.
- Piano completo: [docs/V4-PLAN.md](docs/V4-PLAN.md). THN, con TNN e TNQ, resta nella V7 insieme a TFA in [docs/ROADMAP.md](docs/ROADMAP.md).

Gli esperimenti sono esclusi da Git e conservati sul disco Windows del worktree. Non cancellarli e non ricrearli sopra le directory esistenti. La directory originale `C:/Users/ppell/Desktop/Github/Fang` contiene altre modifiche locali da preservare.

## Risultati EPR appena verificati

In `experiments/v4-epr-kernel-generator-v5`:

- `blocks-v1`, `blocks-v2`, `blocks-v3`: tutti i 14 casi passano la composizione delle chiamate catturate di rimozione dei quantificatori e naming.
- `assembly-v1`, `assembly-v2`, `assembly-v3`: gli stessi 14 casi passano l'assemblaggio delle clausole nell'ordine originale.
- 56 audit delle equazioni dei blocchi, 14 dell'assemblaggio e uno del lemma generico. Due audit dei limiti dei predicati booleani usano solo `propext`; tutti gli altri usano esattamente `propext`, `Classical.choice` e `Quot.sound`.
- Quattro osservazioni alterate sono rifiutate senza un `.olean` accettato: indice del prossimo predicato, arità della definizione, polarità di un letterale, rimozione delle clausole.
- `protocol-v1`: 16 rifiuti tipizzati, senza output parziale.
- `import-closure-v1/check`: 524 coppie sorgente/artefatto, 16 radici e 9 nomi di import esterni verificati.

Receipt: `experiments/v4-epr-kernel-generator-v5/assembly-receipt.json`.

SHA-256: `1d10b93bc2c83a98f9d55ecc01410561236dc3ac24545d957153b1b553878a07`.

Il receipt usa gli snapshot immutabili `rust-v1` e `rust-v2`. Non confrontare il vecchio snapshot con il generatore corrente: quest'ultimo contiene già il lavoro successivo. Il finalizzatore verifica gli snapshot corrispondenti e gli artefatti riutilizzati. Questo risultato resta isolato e non qualifica il percorso EPR installato.

## Punto esatto da riprendere

Il generatore corrente aggiunge lo stadio `conversion` in `src/conversion.rs`. Emette la tabella finale dei predicati, la conversione dei letterali, la rinumerazione e l'equazione `Integration.Named.finishWith`. Tutto il Rust continua a vietare `unsafe`.

1. `rust-v3` passava i controlli Rust, ma `conversion-v1/cnf` falliva in Lean: mancavano i limiti espliciti per le dimensioni e la dimostrazione di `List.Forall₂` sui letterali. Nessun modulo accettato.
2. `rust-v4` corregge i limiti. In `conversion-v2/cnf`, `encode_clause0_eq` passa con i tre assiomi previsti; la corrispondenza dei letterali resta incompleta e il controllo rigoroso segnala argomenti `simp` inutilizzati. Nessun modulo accettato.
3. `rust-v5` corregge il generatore della corrispondenza, distinguendo clausole vuote, uguaglianze e predicati. Formatting, Clippy, test dei limiti condivisi e build release passano. Questo è lo snapshot corrente.
4. Il test `conversion-v3`, avviato per `cnf universal variables boolean-fof`, è stato interrotto su richiesta di pausa mentre verificava il primo caso CNF. `run.exit` vale `143`; non esiste `cnf/GeneratedConversion.olean`. Non è un successo né un nuovo fallimento della prova: non c'è un risultato terminale del controllo Lean.

Sessione terminata: `57647`. Scope terminato: `run-p349-i3192.scope`. Non riutilizzare la directory `conversion-v3` e non dichiarare passata la seconda correzione.

Alla ripresa, dopo aver controllato lo stato corrente, il primo comando previsto è:

```sh
wsl -d Ubuntu -- systemd-run --user --scope -p MemoryMax=4G -p MemorySwapMax=0 -p TasksMax=512 timeout 1800 bash /mnt/c/Users/ppell/Desktop/Github/_scratch/fang-v4-start-20261114/experiments/v4-epr-kernel-generator-v5/check-conversion.sh v4 cnf universal variables boolean-fof
```

Il controller usa il binario immutabile `rust-v5/generator`. Mantiene i limiti precedenti: Lean a un thread, massimo 240 secondi per modulo, due milioni di heartbeat e scope da 4 GiB senza swap. Rigenera gli otto stadi precedenti e verifica l'identità dei sorgenti prima di riutilizzare gli `.olean`. Conservare tutti i fallimenti; non aumentare i limiti per ottenere un passaggio.

Dopo la correzione: completare i 14 casi, i controlli con conversioni alterate e la verifica degli import; collegare `Signed.replayNamedTask`, il replay del certificato e i teoremi di accettazione sui byte originali. Poi revisione indipendente e integrazione nel prodotto. Non sostituire la revisione indipendente con un'autoverifica.

## Resto della V4

AVATAR non è ancora implementato. Restano anche selezione e validazione delle strategie, integrazioni in attesa di revisione, altri punti di input/modelli/certificati e la qualifica finale. La checklist conserva tutte le attività aperte. SWC279-1 passa i controlli ripetuti conservati, ma la causa del vecchio timeout non è stata spiegata.

Il benchmark finale deve confrontare Fang V4 senza check Lean, con check predefinito e con kernel check contro lo stesso Vampire. Conservare formato, liste TXT con le occorrenze originali, tempi per problema e HTML verde/rosso. Nessun confronto con V2. Non usare i tempi di sviluppo come risultati di performance; validation e held-out restano separati dal training. Nessuna release V4 o affermazione SOTA è giustificata ora.

## Arresto

Il test attivo è stato fermato con SIGTERM; il controller registra `143`. Il controllo successivo dei processi Ubuntu non trova compilazioni, test, benchmark o scope Fang in esecuzione. Restavano soltanto servizi di sistema e le shell della verifica. Non sono stati avviati nuovi test dopo la richiesta di pausa.
