# ping.pub for localnet

```sh
docker build -t pingpub .
docker run --rm -p 80:80 pingpub
```

Open `http://0.0.0.0:80` on the browser.
