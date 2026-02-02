# BHPX (Foundation v1)

Minimal Tkinter desktop app for importing:
- **BHP Export (XLSX)** → `shipments`
- **BHP Uplate (CSV, delimiter `;`)** → `payments`

## Run

```powershell
python .\BHPX.py
```

## Dependency

XLSX import requires `openpyxl`:

```powershell
pip install -r .\requirements.txt
```

## Database

SQLite database is created at `data/bhpx.sqlite3`.

## Blagajna (v1)

- Tab **Blagajna** generiše snapshot stavki za izabrani `(year, month)` iz:
  - ULaz: `shipments.cod_amount_minor` po `pickup_date`
  - IZlaz: `payments.paid_amount_minor` po `paid_date`
- `Close month` zaključava mjesec i prenosi saldo u sljedeći mjesec.
- `Unlock` je potreban za izmjene u CLOSED mjesecu (v1 password je hardcoded u `BHPX.py` kao `CASHBOOK_UNLOCK_PASSWORD`).
