# LIDT Publication Report

Publication date: 2026-10-29.

The final LIDT descriptions were applied exactly as supplied in the final manifests:

- 449 theorem descriptions patched.
- 231 definition descriptions patched through the documented theorem-record endpoint.
- 680/680 entries read back with byte-for-byte matching text before publication.
- 680/680 entries made public: 449 theorems and 231 definitions.
- 680/680 entries returned the exact final text and `visibility: public` in an authenticated post-publication audit.
- 680/680 signed-out page checks passed: HTTP 200 and the first sentence of the final text was present, consisting of 449 theorem pages and 231 definition records.
- 0 terms or licensing errors.

For signed-out verification, theorem pages were fetched without an Authorization header and without cookies at no more than two requests per second. Definition records use the working public URL pattern `https://prove2.me/theorems/<definition-id>`; the `/definitions/<id>` probe returned 404, so no definition URL pattern was used. The page audit is recorded in `prove2me/records/lidt_page_verify.json`.

The Prove2Me API returns HTTP 401 for no-token API GETs by design. This is recorded as API behavior, not as a publication failure. No entry is left private according to the authenticated visibility audit.

Public main theorem URL: https://prove2.me/theorems/b2e0f20e-0ffa-46f6-b8a9-3853a661b399

The resumable call state and call log are in `prove2me/records/lidt_publish_state.json` and `prove2me/records/lidt_publish.log`.
