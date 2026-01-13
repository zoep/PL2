# Using mdBook

mdBook is a command-line tool for creating books from Markdown files.

## Installation

```bash
cargo install mdbook
```

## Project Structure

```
book/
├── book.toml          # Configuration file
└── src/
    ├── SUMMARY.md     # Book structure (table of contents)
    └── *.md           # Chapter files
```

## Common Commands

**Serve locally** (watch for changes):
```bash
mdbook serve
```
Opens the book at `http://localhost:3000`

**Build static HTML**:
```bash
mdbook build
```
Output goes to `book/` directory

**Create new book**:
```bash
mdbook init <directory>
```