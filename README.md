# 注意
このリポジトリのソースコードは個人用に作られています。自分が普段使うコマンドのみを考慮しています。
# CoqLint.c
Coqのソースコードを受け取って整形されたソースコードを返す。以下のような整形をする。
- 無駄なスペースや改行を消す
- `match A with B`のような場合分けで適切に改行しインデントを追加する